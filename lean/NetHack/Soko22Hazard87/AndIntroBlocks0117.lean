import NetHack.Soko22Hazard87.AndIntroBlocks0116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro29250 (p : Pattern) (ha : d13575 p = 1) (hb : d94755 p = 1) : d150958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d94755 q = 1) : d150949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29249 q ha hb
    | true =>
      simp only [d13570, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d94755 q = 1) : d150950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d94755 q = 1) : d150955 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d150955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d150955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d94755 q = 1) : d150956 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d150956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d150956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d94755 q = 1) : d150957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d150957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d150957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d94755 q = 1) : d150958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d150958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d150958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29251 (p : Pattern) (ha : d94755 p = 1) (hb : d115464 p = 1) : d150966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d94755 q = 1) : d150959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d150959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29247 q ha hb
    | true =>
      simp only [d13529, d150959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29248 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115460 q = 1) : d150960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d150960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115460, d150960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d94755 q = 1) : d150961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d150961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29250 q ha hb
    | true =>
      simp only [d13576, d150961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d94755 q = 1) : d150962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d150962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d150962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115461 q = 1) : d150963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d150963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d150963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115462 q = 1) : d150964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d150964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115462, d150964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115463 q = 1) : d150965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d150965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115463, d150965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115464 q = 1) : d150966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d150966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115464, d150966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29252 (p : Pattern) (ha : d94755 p = 1) (hb : d115470 p = 1) : d150972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d94755 q = 1) : d150870 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d150870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d150870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29216 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d94755 q = 1) : d150871 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d150871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d150871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d94755 q = 1) : d150879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d150879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29216 q ha hb
    | true =>
      simp only [d13324, d150879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29219 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d94755 q = 1) : d150880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d150880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d150880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d94755 q = 1) : d150881 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d150881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d150881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115448 q = 1) : d150927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d150927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29235 q ha hb
    | true =>
      simp only [d115448, d150927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29243 q ha hb
  have h7 (q : Pattern) (ha : d13467 q = 1) (hb : d94755 q = 1) : d150929 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d150929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29222 q ha hb
    | true =>
      simp only [d13467, d150929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29223 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115449 q = 1) : d150930 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d150930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d150930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115450 q = 1) : d150931 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d150931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115450, d150931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115451 q = 1) : d150932 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d150932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115451, d150932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115455 q = 1) : d150936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d150936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115455, d150936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29244 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29224 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115456 q = 1) : d150937 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d150937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115456, d150937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115457 q = 1) : d150938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d150938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115457, d150938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115458 q = 1) : d150939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d150939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115458, d150939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115459 q = 1) : d150940 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d150940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115459, d150940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115465 q = 1) : d150967 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d150967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115465, d150967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29251 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29227 q ha hb
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115466 q = 1) : d150968 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d150968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115466, d150968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115467 q = 1) : d150969 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d150969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115467, d150969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115468 q = 1) : d150970 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d150970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115468, d150970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d94755 q = 1) (hb : d115469 q = 1) : d150971 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d150971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115469, d150971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115470 q = 1) : d150972 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d150972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115470, d150972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29253 (p : Pattern) (ha : d94755 p = 1) (hb : d115476 p = 1) : d150978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115471 q = 1) : d150973 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d150973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115471, d150973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29252 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115472 q = 1) : d150974 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d150974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115472, d150974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115473 q = 1) : d150975 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d150975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115473, d150975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115474 q = 1) : d150976 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d150976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115474, d150976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115475 q = 1) : d150977 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d150977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115475, d150977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115476 q = 1) : d150978 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d150978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115476, d150978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29254 (p : Pattern) (ha : d13620 p = 1) (hb : d94755 p = 1) : d150985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5255 q = 1) (hb : d94753 q = 1) : d5255 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13613 q = 1) (hb : d94755 q = 1) : d150983 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d94755, d150983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13613, d94755, d150983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13617 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13618 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13618, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13619 q = 1) (hb : d94755 q = 1) : d150984 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d150984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13619, d150984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13620 q = 1) (hb : d94755 q = 1) : d150985 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d150985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13620, d150985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29255 (p : Pattern) (ha : d13624 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13617 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13618 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13618, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13623 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13624 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29256 (p : Pattern) (ha : d13630 p = 1) (hb : d94755 p = 1) : d150991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d94755 q = 1) : d150990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13630 q = 1) (hb : d94755 q = 1) : d150991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d150991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d150991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29257 (p : Pattern) (ha : d13634 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13634 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29258 (p : Pattern) (ha : d13640 p = 1) (hb : d94755 p = 1) : d150997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d94755 q = 1) : d150992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29256 q ha hb
    | true =>
      simp only [d13635, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29257 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d94755 q = 1) : d150993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d150993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d150993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d94755 q = 1) : d150994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d150994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d150994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d94755 q = 1) : d150995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d150995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d150995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d94755 q = 1) : d150996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d150996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d150996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13640 q = 1) (hb : d94755 q = 1) : d150997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d150997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d150997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29259 (p : Pattern) (ha : d13643 p = 1) (hb : d94755 p = 1) : d151000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d94755 q = 1) : d150990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13643 q = 1) (hb : d94755 q = 1) : d151000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d151000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13643, d151000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29260 (p : Pattern) (ha : d13644 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13644 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29261 (p : Pattern) (ha : d13650 p = 1) (hb : d94755 p = 1) : d151006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d94755 q = 1) : d150992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29256 q ha hb
    | true =>
      simp only [d13635, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29257 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d94755 q = 1) : d150993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d150993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d150993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d94755 q = 1) : d150994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d150994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d150994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d94755 q = 1) : d150995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d150995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d150995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d94755 q = 1) : d150996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d150996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d150996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13645 q = 1) (hb : d94755 q = 1) : d151001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29259 q ha hb
    | true =>
      simp only [d13645, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29260 q ha hb
  have h7 (q : Pattern) (ha : d13646 q = 1) (hb : d94755 q = 1) : d151002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d151002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d151002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13647 q = 1) (hb : d94755 q = 1) : d151003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d151003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13647, d151003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13648 q = 1) (hb : d94755 q = 1) : d151004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d151004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d151004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13649 q = 1) (hb : d94755 q = 1) : d151005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d151005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d151005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13650 q = 1) (hb : d94755 q = 1) : d151006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d151006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13650, d151006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29262 (p : Pattern) (ha : d13693 p = 1) (hb : d94755 p = 1) : d150985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5255 q = 1) (hb : d94753 q = 1) : d5255 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13613 q = 1) (hb : d94755 q = 1) : d150983 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d94755, d150983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13613, d94755, d150983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5255 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5256 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5256, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13692 q = 1) (hb : d94755 q = 1) : d150984 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d150984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13692, d150984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13693 q = 1) (hb : d94755 q = 1) : d150985 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d150985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13693, d150985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29263 (p : Pattern) (ha : d13703 p = 1) (hb : d94755 p = 1) : d150991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29262 q ha hb
    | true =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d94755 q = 1) : d150990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13703 q = 1) (hb : d94755 q = 1) : d150991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d150991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d150991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29264 (p : Pattern) (ha : d13787 p = 1) (hb : d94755 p = 1) : d151056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13777 q = 1) (hb : d94755 q = 1) : d150992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29263 q ha hb
    | true =>
      simp only [d13777, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29257 q ha hb
  have h2 (q : Pattern) (ha : d13778 q = 1) (hb : d94755 q = 1) : d150993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d150993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d150993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13779 q = 1) (hb : d94755 q = 1) : d150994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d150994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13779, d150994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13780 q = 1) (hb : d94755 q = 1) : d150995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d150995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d150995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13781 q = 1) (hb : d94755 q = 1) : d150996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d150996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d150996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13782 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29257 q ha hb
    | true =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13783 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13784 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13785 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13786 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13787 q = 1) (hb : d94755 q = 1) : d151056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d151056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13787, d151056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29265 (p : Pattern) (ha : d13793 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13782 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29257 q ha hb
    | true =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13783 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13784 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13785 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13786 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13788 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29260 q ha hb
    | true =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13789 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13790 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13791 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13792 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13793 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29266 (p : Pattern) (ha : d13802 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13788 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29260 q ha hb
    | true =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13789 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13790 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13791 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13792 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13802 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29267 (p : Pattern) (ha : d13849 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13846 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13847 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13847, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13848 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13849 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro29268 (p : Pattern) (ha : d13913 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13850 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29267 q ha hb
    | true =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13851 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13910 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13911 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13912 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13913 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29269 (p : Pattern) (ha : d13919 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13914 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29268 q ha hb
    | true =>
      simp only [d13914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13915 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13916 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13917 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13918 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13919 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29270 (p : Pattern) (ha : d13655 p = 1) (hb : d94755 p = 1) : d151011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d94755 q = 1) : d151010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d151010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d151010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13655 q = 1) (hb : d94755 q = 1) : d151011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d151011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d151011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29271 (p : Pattern) (ha : d13657 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13657 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29272 (p : Pattern) (ha : d13664 p = 1) (hb : d94755 p = 1) : d151018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d94755 q = 1) : d151016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d151016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d151016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d94755 q = 1) : d151017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d151017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d151017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13664 q = 1) (hb : d94755 q = 1) : d151018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d151018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d151018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29273 (p : Pattern) (ha : d13667 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29274 (p : Pattern) (ha : d13689 p = 1) (hb : d94755 p = 1) : d151024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13686 q = 1) (hb : d94753 q = 1) : d13686 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13687 q = 1) (hb : d94755 q = 1) : d151022 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d94755, d151022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13687, d94755, d151022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13612 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5255 q = 1) (hb : d94753 q = 1) : d5255 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13613 q = 1) (hb : d94755 q = 1) : d150983 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d94755, d150983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13613, d94755, d150983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13688 q = 1) (hb : d94755 q = 1) : d151023 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d151023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13688, d151023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13689 q = 1) (hb : d94755 q = 1) : d151024 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d151024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13689, d151024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29275 (p : Pattern) (ha : d13699 p = 1) (hb : d94755 p = 1) : d151030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d94755 q = 1) : d151025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d151025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29274 q ha hb
    | true =>
      simp only [d13690, d151025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d94755 q = 1) : d151026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d151026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d151026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29262 q ha hb
    | true =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d94755 q = 1) : d151027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d151027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d151027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d94755 q = 1) : d151028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d151028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d151028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d94755 q = 1) : d151029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d151029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d151029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d94755 q = 1) : d151030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d151030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d151030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29276 (p : Pattern) (ha : d13744 p = 1) (hb : d94755 p = 1) : d150991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d94755 q = 1) : d150990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d94755 q = 1) : d150991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d150991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d150991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29277 (p : Pattern) (ha : d94755 p = 1) (hb : d115485 p = 1) : d151037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d94755 q = 1) : d151012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d151012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29270 q ha hb
    | true =>
      simp only [d13658, d151012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29271 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d94755 q = 1) : d151013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d151013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d151013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d94755 q = 1) : d151014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d151014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d151014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d94755 q = 1) : d151015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d151015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d151015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d94755 q = 1) : d151019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d151019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29272 q ha hb
    | true =>
      simp only [d13668, d151019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29273 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d94755 q = 1) : d151020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d151020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d151020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d94755 q = 1) : d151021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d151021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d151021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d94755 q = 1) : d151031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d151031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29275 q ha hb
    | true =>
      simp only [d13704, d151031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29263 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115481 q = 1) : d151032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d151032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115481, d151032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d94755 q = 1) : d150992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29276 q ha hb
    | true =>
      simp only [d13745, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d94755 q = 1) : d151033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d151033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d151033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115482 q = 1) : d151034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d151034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d151034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115483 q = 1) : d151035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d151035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115483, d151035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115484 q = 1) : d151036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d151036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115484, d151036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115485 q = 1) : d151037 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d151037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115485, d151037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29278 (p : Pattern) (ha : d13751 p = 1) (hb : d94755 p = 1) : d151038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d94755 q = 1) : d151010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d151010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d151010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13751 q = 1) (hb : d94755 q = 1) : d151038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d151038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13751, d151038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29279 (p : Pattern) (ha : d13752 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13752 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29280 (p : Pattern) (ha : d13757 p = 1) (hb : d94755 p = 1) : d151043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d94755 q = 1) : d151016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d151016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d151016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d94755 q = 1) : d151017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d151017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d151017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13757 q = 1) (hb : d94755 q = 1) : d151043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d151043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13757, d151043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29281 (p : Pattern) (ha : d13758 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13758 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29282 (p : Pattern) (ha : d13762 p = 1) (hb : d94755 p = 1) : d151047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d94755 q = 1) : d151025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d151025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29274 q ha hb
    | true =>
      simp only [d13690, d151025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d94755 q = 1) : d151026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d151026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d151026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29262 q ha hb
    | true =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d94755 q = 1) : d151027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d151027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d151027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d94755 q = 1) : d151028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d151028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d151028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d94755 q = 1) : d151029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d151029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d151029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d94755 q = 1) : d151047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d151047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d151047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29283 (p : Pattern) (ha : d13763 p = 1) (hb : d94755 p = 1) : d151000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29262 q ha hb
    | true =>
      simp only [d13694, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29255 q ha hb
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d94755 q = 1) : d150990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13763 q = 1) (hb : d94755 q = 1) : d151000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d151000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13763, d151000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29284 (p : Pattern) (ha : d13769 p = 1) (hb : d94755 p = 1) : d151000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d94755 q = 1) : d150986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29254 q ha hb
    | true =>
      simp only [d13621, d150986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d94755 q = 1) : d150987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d150987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d94755 q = 1) : d150988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d150988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d94755 q = 1) : d150989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d150989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d94755 q = 1) : d150990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d150990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d94755 q = 1) : d151000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d151000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d151000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29285 (p : Pattern) (ha : d94755 p = 1) (hb : d115490 p = 1) : d151054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d94755 q = 1) : d151012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d151012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29270 q ha hb
    | true =>
      simp only [d13658, d151012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29271 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d94755 q = 1) : d151013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d151013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d151013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d94755 q = 1) : d151014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d151014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d151014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d94755 q = 1) : d151015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d151015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d151015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d94755 q = 1) : d151019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d151019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29272 q ha hb
    | true =>
      simp only [d13668, d151019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29273 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d94755 q = 1) : d151020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d151020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d151020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d94755 q = 1) : d151021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d151021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d151021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d94755 q = 1) : d151031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d151031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29275 q ha hb
    | true =>
      simp only [d13704, d151031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29263 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115481 q = 1) : d151032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d151032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d115481, d151032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d94755 q = 1) : d150992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29276 q ha hb
    | true =>
      simp only [d13745, d150992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d94755 q = 1) : d151033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d151033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d151033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115482 q = 1) : d151034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d151034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d151034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115483 q = 1) : d151035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d151035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d115483, d151035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115484 q = 1) : d151036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d151036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d115484, d151036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13753 q = 1) (hb : d94755 q = 1) : d151039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d151039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29278 q ha hb
    | true =>
      simp only [d13753, d151039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29279 q ha hb
  have h16 (q : Pattern) (ha : d13754 q = 1) (hb : d94755 q = 1) : d151040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d151040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d151040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13755 q = 1) (hb : d94755 q = 1) : d151041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d151041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13755, d151041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13756 q = 1) (hb : d94755 q = 1) : d151042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d151042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d151042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13759 q = 1) (hb : d94755 q = 1) : d151044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d151044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29280 q ha hb
    | true =>
      simp only [d13759, d151044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29281 q ha hb
  have h20 (q : Pattern) (ha : d13760 q = 1) (hb : d94755 q = 1) : d151045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d151045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d151045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13761 q = 1) (hb : d94755 q = 1) : d151046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d151046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13761, d151046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13764 q = 1) (hb : d94755 q = 1) : d151048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d151048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29282 q ha hb
    | true =>
      simp only [d13764, d151048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29283 q ha hb
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115486 q = 1) : d151049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d151049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d115486, d151049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d13770 q = 1) (hb : d94755 q = 1) : d151001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29284 q ha hb
    | true =>
      simp only [d13770, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13771 q = 1) (hb : d94755 q = 1) : d151050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d151050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13771, d151050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94755 q = 1) (hb : d115487 q = 1) : d151051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d151051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115487, d151051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d94755 q = 1) (hb : d115488 q = 1) : d151052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d151052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d115488, d151052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94755 q = 1) (hb : d115489 q = 1) : d151053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d151053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d115489, d151053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94755 q = 1) (hb : d115490 q = 1) : d151054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d151054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115490, d151054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29286 (p : Pattern) (ha : d94755 p = 1) (hb : d115497 p = 1) : d151063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d94755 q = 1) : d151048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d151048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29282 q ha hb
    | true =>
      simp only [d13764, d151048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29283 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115486 q = 1) : d151049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d151049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115486, d151049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d94755 q = 1) : d151001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29284 q ha hb
    | true =>
      simp only [d13770, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d94755 q = 1) : d151050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d151050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d151050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115487 q = 1) : d151051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d151051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d151051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115495 q = 1) : d151061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d151061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115495, d151061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115496 q = 1) : d151062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d151062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115496, d151062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115497 q = 1) : d151063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d151063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115497, d151063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29287 (p : Pattern) (ha : d13832 p = 1) (hb : d94755 p = 1) : d151072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13812 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13825 q = 1) (hb : d94753 q = 1) : d13825 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13826 q = 1) (hb : d94755 q = 1) : d151069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d94755, d151069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13826, d94755, d151069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13829 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6651 q = 1) (hb : d94753 q = 1) : d6651 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13830 q = 1) (hb : d94755 q = 1) : d151070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d94755, d151070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13830, d94755, d151070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13831 q = 1) (hb : d94755 q = 1) : d151071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d151071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13831, d151071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13832 q = 1) (hb : d94755 q = 1) : d151072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d151072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13832, d151072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29288 (p : Pattern) (ha : d13836 p = 1) (hb : d94755 p = 1) : d151076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13829 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6651 q = 1) (hb : d94753 q = 1) : d6651 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13830 q = 1) (hb : d94755 q = 1) : d151070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d94755, d151070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13830, d94755, d151070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6651 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6652 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d6652, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13835 q = 1) (hb : d94755 q = 1) : d151075 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d151075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13835, d151075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13836 q = 1) (hb : d94755 q = 1) : d151076 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d151076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13836, d151076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29289 (p : Pattern) (ha : d13842 p = 1) (hb : d94755 p = 1) : d151082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d94755 q = 1) : d151073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d151073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29287 q ha hb
    | true =>
      simp only [d13833, d151073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d94755 q = 1) : d151074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d151074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d151074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d94755 q = 1) : d151077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29288 q ha hb
    | true =>
      simp only [d13837, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d94755 q = 1) : d151078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d94755 q = 1) : d151079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d151079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d151079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d94755 q = 1) : d151080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d151080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d151080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d94755 q = 1) : d151081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d151081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d151081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d94755 q = 1) : d151082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d151082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d151082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29290 (p : Pattern) (ha : d13855 p = 1) (hb : d94755 p = 1) : d151086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d94755 q = 1) : d151077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29288 q ha hb
    | true =>
      simp only [d13837, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d94755 q = 1) : d151078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29267 q ha hb
    | true =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13852 q = 1) (hb : d94755 q = 1) : d151083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d151083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d151083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13853 q = 1) (hb : d94755 q = 1) : d151084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d151084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13853, d151084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13854 q = 1) (hb : d94755 q = 1) : d151085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d151085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13854, d151085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13855 q = 1) (hb : d94755 q = 1) : d151086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d151086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13855, d151086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29291 (p : Pattern) (ha : d13896 p = 1) (hb : d94755 p = 1) : d151076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13829 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6651 q = 1) (hb : d94753 q = 1) : d6651 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13830 q = 1) (hb : d94755 q = 1) : d151070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d94755, d151070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13830, d94755, d151070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13846 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13847 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d13847, d94755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13895 q = 1) (hb : d94755 q = 1) : d151075 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d151075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13895, d151075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13896 q = 1) (hb : d94755 q = 1) : d151076 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d151076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13896, d151076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29292 (p : Pattern) (ha : d13902 p = 1) (hb : d94755 p = 1) : d151086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d94755 q = 1) : d151077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29291 q ha hb
    | true =>
      simp only [d13897, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d94755 q = 1) : d151078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d94755 q = 1) : d151083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d151083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d151083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d94755 q = 1) : d151084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d151084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d151084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d94755 q = 1) : d151085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d151085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d151085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d94755 q = 1) : d151086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d151086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d151086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29293 (p : Pattern) (ha : d94755 p = 1) (hb : d115507 p = 1) : d151094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d94755 q = 1) : d151087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d151087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29289 q ha hb
    | true =>
      simp only [d13856, d151087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29290 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115503 q = 1) : d151088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d151088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115503, d151088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d94755 q = 1) : d151089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d151089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29292 q ha hb
    | true =>
      simp only [d13903, d151089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d94755 q = 1) : d151090 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d151090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d151090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115504 q = 1) : d151091 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d151091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d151091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115505 q = 1) : d151092 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d151092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115505, d151092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115506 q = 1) : d151093 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d151093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115506, d151093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115507 q = 1) : d151094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d151094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115507, d151094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29294 (p : Pattern) (ha : d94755 p = 1) (hb : d115513 p = 1) : d151100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d94755 q = 1) : d150998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d150998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d150998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29258 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d94755 q = 1) : d150999 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d150999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d150999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d94755 q = 1) : d151007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d151007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29258 q ha hb
    | true =>
      simp only [d13651, d151007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29261 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d94755 q = 1) : d151008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d151008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d151008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d94755 q = 1) : d151009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d151009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d151009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115491 q = 1) : d151055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d151055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29277 q ha hb
    | true =>
      simp only [d115491, d151055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29285 q ha hb
  have h7 (q : Pattern) (ha : d13794 q = 1) (hb : d94755 q = 1) : d151057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d151057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29264 q ha hb
    | true =>
      simp only [d13794, d151057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29265 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115492 q = 1) : d151058 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d151058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d151058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115493 q = 1) : d151059 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d151059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115493, d151059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115494 q = 1) : d151060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d151060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d115494, d151060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115498 q = 1) : d151064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d151064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115498, d151064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29286 q ha hb
  have h12 (q : Pattern) (ha : d13803 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29266 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115499 q = 1) : d151065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d151065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115499, d151065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115500 q = 1) : d151066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d151066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115500, d151066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115501 q = 1) : d151067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d151067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115501, d151067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115502 q = 1) : d151068 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d151068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115502, d151068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94755 q = 1) (hb : d115508 q = 1) : d151095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d151095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115508, d151095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29293 q ha hb
  have h18 (q : Pattern) (ha : d13920 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29269 q ha hb
  have h19 (q : Pattern) (ha : d94755 q = 1) (hb : d115509 q = 1) : d151096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d151096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115509, d151096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d94755 q = 1) (hb : d115510 q = 1) : d151097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d151097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115510, d151097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d94755 q = 1) (hb : d115511 q = 1) : d151098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d151098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115511, d151098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d94755 q = 1) (hb : d115512 q = 1) : d151099 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d151099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115512, d151099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d94755 q = 1) (hb : d115513 q = 1) : d151100 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d151100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115513, d151100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29295 (p : Pattern) (ha : d94755 p = 1) (hb : d115519 p = 1) : d151106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115514 q = 1) : d151101 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d151101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115514, d151101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29294 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115515 q = 1) : d151102 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d151102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115515, d151102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115516 q = 1) : d151103 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d151103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115516, d151103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115517 q = 1) : d151104 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d151104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115517, d151104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115518 q = 1) : d151105 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d151105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115518, d151105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115519 q = 1) : d151106 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d151106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115519, d151106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29296 (p : Pattern) (ha : d94755 p = 1) (hb : d115525 p = 1) : d151112 p = 1 := by
  have h0 (q : Pattern) (ha : d94755 q = 1) (hb : d115354 q = 1) : d150664 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d150664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29093 q ha hb
    | true =>
      simp only [d115354, d150664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29131 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115394 q = 1) : d150726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d150726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115394, d150726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29169 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115395 q = 1) : d150727 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d150727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d150727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115435 q = 1) : d150852 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d150852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115435, d150852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29211 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115436 q = 1) : d150853 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d150853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115436, d150853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115437 q = 1) : d150854 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d150854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d150854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d115477 q = 1) : d150979 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d150979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115477, d150979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29253 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d115478 q = 1) : d150980 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d150980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115478, d150980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d115479 q = 1) : d150981 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d150981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115479, d150981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d115480 q = 1) : d150982 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d150982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d150982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d115520 q = 1) : d151107 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d151107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115520, d151107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29295 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d115521 q = 1) : d151108 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d151108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115521, d151108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d115522 q = 1) : d151109 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d151109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115522, d151109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d115523 q = 1) : d151110 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d151110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115523, d151110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d115524 q = 1) : d151111 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d151111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d151111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d115525 q = 1) : d151112 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d151112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d151112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro29297 (p : Pattern) (ha : d94755 p = 1) (hb : d115531 p = 1) : d151118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115526 q = 1) : d151113 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d151113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29296 q ha hb
    | true =>
      simp only [d115526, d151113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115527 q = 1) : d151114 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d151114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d151114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115528 q = 1) : d151115 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d151115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d151115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115529 q = 1) : d151116 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d151116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d151116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115530 q = 1) : d151117 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d151117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d151117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115531 q = 1) : d151118 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d151118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d151118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29298 (p : Pattern) (ha : d94755 p = 1) (hb : d115537 p = 1) : d151124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115532 q = 1) : d151119 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d151119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29297 q ha hb
    | true =>
      simp only [d115532, d151119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115533 q = 1) : d151120 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d151120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d151120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115534 q = 1) : d151121 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d151121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d151121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115535 q = 1) : d151122 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d151122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d151122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115536 q = 1) : d151123 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d151123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d151123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115537 q = 1) : d151124 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d151124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d151124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29299 (p : Pattern) (ha : d94755 p = 1) (hb : d115543 p = 1) : d151130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115538 q = 1) : d151125 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d151125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29298 q ha hb
    | true =>
      simp only [d115538, d151125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115539 q = 1) : d151126 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d151126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d151126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115540 q = 1) : d151127 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d151127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d151127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115541 q = 1) : d151128 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d151128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d151128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115542 q = 1) : d151129 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d151129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d151129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115543 q = 1) : d151130 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d151130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d151130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29300 (p : Pattern) (ha : d94755 p = 1) (hb : d115549 p = 1) : d151136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115544 q = 1) : d151131 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d151131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29299 q ha hb
    | true =>
      simp only [d115544, d151131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115545 q = 1) : d151132 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d151132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d151132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d115546 q = 1) : d151133 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d151133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d151133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d115547 q = 1) : d151134 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d151134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d151134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d115548 q = 1) : d151135 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d151135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d151135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d115549 q = 1) : d151136 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d151136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d151136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29301 (p : Pattern) (ha : d94756 p = 1) (hb : d115555 p = 1) : d151142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d115550 q = 1) : d151137 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d151137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29300 q ha hb
    | true =>
      simp only [d115550, d151137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d115551 q = 1) : d151138 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d151138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d151138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94756 q = 1) (hb : d115552 q = 1) : d151139 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94756, d115552, d151139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94756, d115552, d151139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94756 q = 1) (hb : d115553 q = 1) : d151140 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d151140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115553, d151140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94756 q = 1) (hb : d115554 q = 1) : d151141 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d151141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115554, d151141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d94756 q = 1) (hb : d115555 q = 1) : d151142 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d151142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115555, d151142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro29302 (p : Pattern) (ha : d94756 p = 1) (hb : d115561 p = 1) : d151148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94756 q = 1) (hb : d115556 q = 1) : d151143 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d151143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29301 q ha hb
    | true =>
      simp only [d115556, d151143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94756 q = 1) (hb : d115557 q = 1) : d151144 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d151144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d151144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94756 q = 1) (hb : d115558 q = 1) : d151145 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d151145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d151145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94756 q = 1) (hb : d115559 q = 1) : d151146 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d151146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d151146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94756 q = 1) (hb : d115560 q = 1) : d151147 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d151147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d151147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94756 q = 1) (hb : d115561 q = 1) : d151148 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d151148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d151148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29303 (p : Pattern) (ha : d94756 p = 1) (hb : d115567 p = 1) : d151154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94756 q = 1) (hb : d115562 q = 1) : d151149 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d151149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29302 q ha hb
    | true =>
      simp only [d115562, d151149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94756 q = 1) (hb : d115563 q = 1) : d151150 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d151150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d151150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94756 q = 1) (hb : d115564 q = 1) : d151151 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d151151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d151151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94756 q = 1) (hb : d115565 q = 1) : d151152 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d151152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d151152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94756 q = 1) (hb : d115566 q = 1) : d151153 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d151153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d151153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94756 q = 1) (hb : d115567 q = 1) : d151154 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d151154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d151154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29304 (p : Pattern) (ha : d1 p = 1) (hb : d151154 p = 1) : d151154 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d151154 q = 1) : d151154 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro29305 (p : Pattern) (ha : d94755 p = 1) (hb : d150329 p = 1) : d98290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29066 q ha hb
    | true =>
      simp only [d12241, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
  have h2 (q : Pattern) (ha : d12292 q = 1) (hb : d94755 q = 1) : d97520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12293 q = 1) (hb : d94755 q = 1) : d97521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12293, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12294 q = 1) (hb : d94755 q = 1) : d97522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12295 q = 1) (hb : d94755 q = 1) : d97523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150329 q = 1) : d98290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d98290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150329, d98290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29306 (p : Pattern) (ha : d94755 p = 1) (hb : d150339 p = 1) : d98300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d94755 q = 1) : d97496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29070 q ha hb
    | true =>
      simp only [d12268, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12395 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150335 q = 1) : d98296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d98296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150335, d98296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150336 q = 1) : d98297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d98297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150336, d98297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150337 q = 1) : d98298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d98298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150337, d98298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150338 q = 1) : d98299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d98299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150338, d98299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150339 q = 1) : d98300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d98300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150339, d98300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29307 (p : Pattern) (ha : d94755 p = 1) (hb : d150345 p = 1) : d98306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d94755 q = 1) : d97525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29073 q ha hb
    | true =>
      simp only [d12297, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29074 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d94755 q = 1) : d97526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150327 q = 1) : d98288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d98288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150327, d98288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150328 q = 1) : d98289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d98289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150328, d98289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150330 q = 1) : d98291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d98291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150330, d98291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29305 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150331 q = 1) : d98292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d98292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d98292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150332 q = 1) : d98293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d98293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d98293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150333 q = 1) : d98294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d98294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d98294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150334 q = 1) : d98295 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d98295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d98295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150340 q = 1) : d98301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d98301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150340, d98301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29306 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150341 q = 1) : d98302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d98302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d98302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150342 q = 1) : d98303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d98303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d98303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150343 q = 1) : d98304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d98304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d98304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150344 q = 1) : d98305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d98305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d98305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150345 q = 1) : d98306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d98306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d98306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29308 (p : Pattern) (ha : d94755 p = 1) (hb : d150351 p = 1) : d98312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12910 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150346 q = 1) : d98307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d98307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150346, d98307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29307 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150347 q = 1) : d98308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d98308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150347, d98308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150348 q = 1) : d98309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d98309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150348, d98309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150349 q = 1) : d98310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d98310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150349, d98310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150350 q = 1) : d98311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d98311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150350, d98311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150351 q = 1) : d98312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d98312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150351, d98312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29309 (p : Pattern) (ha : d94755 p = 1) (hb : d150354 p = 1) : d98315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d94755 q = 1) : d97629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29099 q ha hb
    | true =>
      simp only [d12463, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29100 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d94755 q = 1) : d97630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d94755 q = 1) : d97631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d94755 q = 1) : d97632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d94755 q = 1) : d97633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150354 q = 1) : d98315 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d98315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150354, d98315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29310 (p : Pattern) (ha : d94755 p = 1) (hb : d150365 p = 1) : d98325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150360 q = 1) : d97716 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29127 q hb ha
    | true =>
      simp only [d150360, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29106 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150361 q = 1) : d98321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d98321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150361, d98321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150362 q = 1) : d98322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d98322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d98322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150363 q = 1) : d98323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d98323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150363, d98323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150364 q = 1) : d98324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d98324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150364, d98324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150365 q = 1) : d98325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d98325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150365, d98325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29311 (p : Pattern) (ha : d94755 p = 1) (hb : d150371 p = 1) : d98331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d94755 q = 1) : d97635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29098 q ha hb
    | true =>
      simp only [d12469, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29101 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d94755 q = 1) : d97636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150352 q = 1) : d98313 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d98313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150352, d98313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150353 q = 1) : d98314 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d98314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150353, d98314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150355 q = 1) : d98316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d98316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150355, d98316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29309 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150356 q = 1) : d98317 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d98317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d98317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150357 q = 1) : d98318 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d98318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d98318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150358 q = 1) : d98319 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d98319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d98319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150359 q = 1) : d98320 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d98320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d98320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150366 q = 1) : d98326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d98326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150366, d98326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29310 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150367 q = 1) : d98327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d98327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d98327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150368 q = 1) : d98328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d98328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d98328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150369 q = 1) : d98329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d98329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d98329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150370 q = 1) : d98330 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d98330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d98330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150371 q = 1) : d98331 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d98331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d98331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29312 (p : Pattern) (ha : d94755 p = 1) (hb : d150377 p = 1) : d98337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150372 q = 1) : d98332 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d98332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150372, d98332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29311 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150373 q = 1) : d98333 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d98333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150373, d98333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150374 q = 1) : d98334 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d98334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150374, d98334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150375 q = 1) : d98335 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d98335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150375, d98335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150376 q = 1) : d98336 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d98336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150376, d98336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150377 q = 1) : d98337 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d98337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150377, d98337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29313 (p : Pattern) (ha : d94755 p = 1) (hb : d150381 p = 1) : d98341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29137 q ha hb
    | true =>
      simp only [d12718, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29138 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d94755 q = 1) : d97754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d94755 q = 1) : d97755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d94755 q = 1) : d97756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d94755 q = 1) : d97757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150381 q = 1) : d98341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d98341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150381, d98341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29314 (p : Pattern) (ha : d94755 p = 1) (hb : d150392 p = 1) : d98351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150387 q = 1) : d97841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29165 q hb ha
    | true =>
      simp only [d150387, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29144 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150388 q = 1) : d98347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d98347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150388, d98347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150389 q = 1) : d98348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d98348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d98348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150390 q = 1) : d98349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d98349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150390, d98349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150391 q = 1) : d98350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d98350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150391, d98350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150392 q = 1) : d98351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d98351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150392, d98351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29315 (p : Pattern) (ha : d94755 p = 1) (hb : d150398 p = 1) : d98357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d94755 q = 1) : d97759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29136 q ha hb
    | true =>
      simp only [d12724, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29139 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d94755 q = 1) : d97760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150379 q = 1) : d98339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d98339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150379, d98339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150380 q = 1) : d98340 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d98340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150380, d98340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150382 q = 1) : d98342 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d98342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150382, d98342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29313 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150383 q = 1) : d98343 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d98343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d98343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150384 q = 1) : d98344 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d98344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d98344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150385 q = 1) : d98345 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d98345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d98345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150386 q = 1) : d98346 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d98346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d98346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150393 q = 1) : d98352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d98352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150393, d98352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29314 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150394 q = 1) : d98353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d98353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d98353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150395 q = 1) : d98354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d98354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d98354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150396 q = 1) : d98355 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d98355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d98355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150397 q = 1) : d98356 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d98356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d98356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150398 q = 1) : d98357 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d98357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d98357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29316 (p : Pattern) (ha : d94755 p = 1) (hb : d150404 p = 1) : d98363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150399 q = 1) : d98358 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d98358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150399, d98358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29315 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150400 q = 1) : d98359 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d98359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150400, d98359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150401 q = 1) : d98360 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d98360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150401, d98360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150402 q = 1) : d98361 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d98361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150402, d98361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150403 q = 1) : d98362 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d98362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150403, d98362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150404 q = 1) : d98363 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d98363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150404, d98363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29317 (p : Pattern) (ha : d94755 p = 1) (hb : d150409 p = 1) : d151157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d94755 q = 1) : d150746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29175 q ha hb
    | true =>
      simp only [d12992, d150746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29176 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d94755 q = 1) : d150747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d150747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d150747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d94755 q = 1) : d150748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d150748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d150748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d94755 q = 1) : d150749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d150749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d150749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d94755 q = 1) : d150750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d150750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d150750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150409 q = 1) : d151157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d151157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150409, d151157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29318 (p : Pattern) (ha : d94755 p = 1) (hb : d150418 p = 1) : d150831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d94755 q = 1) : d150822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29207 q ha hb
    | true =>
      simp only [d13244, d150822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d94755 q = 1) : d150823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d150823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29183 q ha hb
    | true =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150415 q = 1) : d150828 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d150828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150415, d150828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150416 q = 1) : d150829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d150829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d150829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150417 q = 1) : d150830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d150830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d150830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150418 q = 1) : d150831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d150831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d150831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29319 (p : Pattern) (ha : d94755 p = 1) (hb : d150424 p = 1) : d151167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150419 q = 1) : d150834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d150834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29318 q ha hb
    | true =>
      simp only [d150419, d150834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29184 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150420 q = 1) : d151163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d151163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150420, d151163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150421 q = 1) : d151164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d151164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d151164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150422 q = 1) : d151165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d151165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150422, d151165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150423 q = 1) : d151166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d151166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150423, d151166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150424 q = 1) : d151167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d151167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150424, d151167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29320 (p : Pattern) (ha : d94755 p = 1) (hb : d150430 p = 1) : d151173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d94755 q = 1) : d150752 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d150752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29174 q ha hb
    | true =>
      simp only [d12998, d150752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29177 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d94755 q = 1) : d150753 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d150753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d150753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150407 q = 1) : d151155 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d151155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150407, d151155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150408 q = 1) : d151156 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d151156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150408, d151156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150410 q = 1) : d151158 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d151158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150410, d151158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29317 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150411 q = 1) : d151159 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d151159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d151159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150412 q = 1) : d151160 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d151160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d151160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150413 q = 1) : d151161 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d151161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d151161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150414 q = 1) : d151162 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d151162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d151162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150425 q = 1) : d151168 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d151168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150425, d151168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29319 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150426 q = 1) : d151169 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d151169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d151169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150427 q = 1) : d151170 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d151170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d151170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150428 q = 1) : d151171 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d151171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d151171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150429 q = 1) : d151172 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d151172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d151172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150430 q = 1) : d151173 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d151173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d151173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29321 (p : Pattern) (ha : d94755 p = 1) (hb : d150436 p = 1) : d151179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150431 q = 1) : d151174 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d151174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150431, d151174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29320 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150432 q = 1) : d151175 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d151175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150432, d151175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150433 q = 1) : d151176 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d151176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150433, d151176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150434 q = 1) : d151177 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d151177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150434, d151177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150435 q = 1) : d151178 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d151178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150435, d151178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150436 q = 1) : d151179 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d151179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150436, d151179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29322 (p : Pattern) (ha : d94755 p = 1) (hb : d150442 p = 1) : d151185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d94755 q = 1) : d150873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29217 q ha hb
    | true =>
      simp only [d13318, d150873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29218 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d94755 q = 1) : d150874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d150874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d150874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d94755 q = 1) : d150875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d150875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d150875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d94755 q = 1) : d150876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d150876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d150876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d94755 q = 1) : d150877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d150877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d150877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150442 q = 1) : d151185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d151185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150442, d151185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29323 (p : Pattern) (ha : d94755 p = 1) (hb : d150451 p = 1) : d150958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d94755 q = 1) : d150949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29249 q ha hb
    | true =>
      simp only [d13570, d150949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d94755 q = 1) : d150950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d150950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29225 q ha hb
    | true =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150448 q = 1) : d150955 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d150955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150448, d150955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150449 q = 1) : d150956 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d150956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d150956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150450 q = 1) : d150957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d150957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d150957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150451 q = 1) : d150958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d150958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d150958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29324 (p : Pattern) (ha : d94755 p = 1) (hb : d150457 p = 1) : d151195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150452 q = 1) : d150961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d150961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29323 q ha hb
    | true =>
      simp only [d150452, d150961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29226 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150453 q = 1) : d151191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d151191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150453, d151191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150454 q = 1) : d151192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d151192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d151192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150455 q = 1) : d151193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d151193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150455, d151193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150456 q = 1) : d151194 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d151194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150456, d151194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150457 q = 1) : d151195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d151195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150457, d151195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29325 (p : Pattern) (ha : d94755 p = 1) (hb : d150463 p = 1) : d151201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d94755 q = 1) : d150879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d150879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29216 q ha hb
    | true =>
      simp only [d13324, d150879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29219 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d94755 q = 1) : d150880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d150880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d150880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150440 q = 1) : d151183 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d151183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150440, d151183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150441 q = 1) : d151184 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d151184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150441, d151184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150443 q = 1) : d151186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d151186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150443, d151186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29322 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150444 q = 1) : d151187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d151187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d151187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150445 q = 1) : d151188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d151188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d151188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150446 q = 1) : d151189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d151189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d151189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150447 q = 1) : d151190 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d151190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d151190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150458 q = 1) : d151196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d151196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150458, d151196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29324 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150459 q = 1) : d151197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d151197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d151197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150460 q = 1) : d151198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d151198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d151198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150461 q = 1) : d151199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d151199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d151199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150462 q = 1) : d151200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d151200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d151200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150463 q = 1) : d151201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d151201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d151201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29326 (p : Pattern) (ha : d94755 p = 1) (hb : d150469 p = 1) : d151207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150464 q = 1) : d151202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d151202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150464, d151202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29325 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150465 q = 1) : d151203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d151203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150465, d151203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150466 q = 1) : d151204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d151204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150466, d151204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150467 q = 1) : d151205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d151205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150467, d151205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150468 q = 1) : d151206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d151206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150468, d151206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150469 q = 1) : d151207 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d151207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150469, d151207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29327 (p : Pattern) (ha : d94755 p = 1) (hb : d150476 p = 1) : d151214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d94755 q = 1) : d151001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29259 q ha hb
    | true =>
      simp only [d13645, d151001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29260 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d94755 q = 1) : d151002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d151002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d151002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d94755 q = 1) : d151003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d151003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d151003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d94755 q = 1) : d151004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d151004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d151004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d94755 q = 1) : d151005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d151005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d151005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150476 q = 1) : d151214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d151214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150476, d151214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro29328 (p : Pattern) (ha : d94755 p = 1) (hb : d150485 p = 1) : d151086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d94755 q = 1) : d151077 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29291 q ha hb
    | true =>
      simp only [d13897, d151077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d94755 q = 1) : d151078 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d151078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29267 q ha hb
    | true =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150482 q = 1) : d151083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d151083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150482, d151083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150483 q = 1) : d151084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d151084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d151084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150484 q = 1) : d151085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d151085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d151085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150485 q = 1) : d151086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d151086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d151086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro29329 (p : Pattern) (ha : d94755 p = 1) (hb : d150491 p = 1) : d151224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150486 q = 1) : d151089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d151089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29328 q ha hb
    | true =>
      simp only [d150486, d151089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29268 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150487 q = 1) : d151220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d151220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150487, d151220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150488 q = 1) : d151221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d151221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d151221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150489 q = 1) : d151222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d151222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150489, d151222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150490 q = 1) : d151223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d151223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150490, d151223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150491 q = 1) : d151224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d151224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150491, d151224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29330 (p : Pattern) (ha : d94755 p = 1) (hb : d150497 p = 1) : d151230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d94755 q = 1) : d151007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d151007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29258 q ha hb
    | true =>
      simp only [d13651, d151007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29261 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d94755 q = 1) : d151008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d151008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d151008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150474 q = 1) : d151212 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d151212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150474, d151212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150475 q = 1) : d151213 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d151213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150475, d151213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150477 q = 1) : d151215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d151215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150477, d151215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29327 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150478 q = 1) : d151216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d151216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d151216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150479 q = 1) : d151217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d151217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d151217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150480 q = 1) : d151218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d151218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d151218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150481 q = 1) : d151219 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d151219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d151219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150492 q = 1) : d151225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d151225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150492, d151225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29329 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150493 q = 1) : d151226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d151226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d151226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150494 q = 1) : d151227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d151227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d151227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150495 q = 1) : d151228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d151228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d151228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150496 q = 1) : d151229 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d151229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d151229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150497 q = 1) : d151230 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d151230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d151230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29331 (p : Pattern) (ha : d94755 p = 1) (hb : d150503 p = 1) : d151236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150498 q = 1) : d151231 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d151231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150498, d151231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29330 q ha hb
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150499 q = 1) : d151232 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d151232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150499, d151232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150500 q = 1) : d151233 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d151233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150500, d151233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150501 q = 1) : d151234 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d151234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150501, d151234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150502 q = 1) : d151235 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d151235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150502, d151235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150503 q = 1) : d151236 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d151236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150503, d151236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29332 (p : Pattern) (ha : d94755 p = 1) (hb : d150509 p = 1) : d151242 p = 1 := by
  have h0 (q : Pattern) (ha : d94755 q = 1) (hb : d150378 q = 1) : d98338 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d98338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29308 q ha hb
    | true =>
      simp only [d150378, d98338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29312 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150405 q = 1) : d98364 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d98364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150405, d98364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29316 q ha hb
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150406 q = 1) : d98365 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d98365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d98365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150437 q = 1) : d151180 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d151180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150437, d151180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29321 q ha hb
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150438 q = 1) : d151181 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d151181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150438, d151181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150439 q = 1) : d151182 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d151182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d151182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94755 q = 1) (hb : d150470 q = 1) : d151208 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d151208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150470, d151208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29326 q ha hb
  have h8 (q : Pattern) (ha : d94755 q = 1) (hb : d150471 q = 1) : d151209 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d151209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150471, d151209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94755 q = 1) (hb : d150472 q = 1) : d151210 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d151210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150472, d151210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94755 q = 1) (hb : d150473 q = 1) : d151211 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d151211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d151211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94755 q = 1) (hb : d150504 q = 1) : d151237 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d151237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150504, d151237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29331 q ha hb
  have h12 (q : Pattern) (ha : d94755 q = 1) (hb : d150505 q = 1) : d151238 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d151238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150505, d151238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94755 q = 1) (hb : d150506 q = 1) : d151239 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d151239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150506, d151239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94755 q = 1) (hb : d150507 q = 1) : d151240 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d151240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150507, d151240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94755 q = 1) (hb : d150508 q = 1) : d151241 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d151241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d151241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94755 q = 1) (hb : d150509 q = 1) : d151242 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d151242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d151242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro29333 (p : Pattern) (ha : d94755 p = 1) (hb : d150515 p = 1) : d151248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150510 q = 1) : d151243 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d151243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29332 q ha hb
    | true =>
      simp only [d150510, d151243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150511 q = 1) : d151244 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d151244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d151244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150512 q = 1) : d151245 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d151245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d151245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150513 q = 1) : d151246 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d151246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d151246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150514 q = 1) : d151247 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d151247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d151247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150515 q = 1) : d151248 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d151248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d151248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29334 (p : Pattern) (ha : d94755 p = 1) (hb : d150521 p = 1) : d151254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150516 q = 1) : d151249 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d151249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29333 q ha hb
    | true =>
      simp only [d150516, d151249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150517 q = 1) : d151250 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d151250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d151250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150518 q = 1) : d151251 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d151251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d151251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150519 q = 1) : d151252 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d151252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d151252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150520 q = 1) : d151253 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d151253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d151253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150521 q = 1) : d151254 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d151254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d151254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29335 (p : Pattern) (ha : d94755 p = 1) (hb : d150527 p = 1) : d151260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150522 q = 1) : d151255 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d151255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29334 q ha hb
    | true =>
      simp only [d150522, d151255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150523 q = 1) : d151256 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d151256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d151256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150524 q = 1) : d151257 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d151257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d151257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150525 q = 1) : d151258 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d151258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d151258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150526 q = 1) : d151259 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d151259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d151259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150527 q = 1) : d151260 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d151260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d151260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29336 (p : Pattern) (ha : d94755 p = 1) (hb : d150533 p = 1) : d151266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150528 q = 1) : d151261 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d151261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29335 q ha hb
    | true =>
      simp only [d150528, d151261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150529 q = 1) : d151262 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d151262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d151262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94755 q = 1) (hb : d150530 q = 1) : d151263 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d151263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d151263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94755 q = 1) (hb : d150531 q = 1) : d151264 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d151264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d151264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94755 q = 1) (hb : d150532 q = 1) : d151265 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d151265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d151265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94755 q = 1) (hb : d150533 q = 1) : d151266 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d151266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d151266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29337 (p : Pattern) (ha : d94756 p = 1) (hb : d150539 p = 1) : d151272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94755 q = 1) (hb : d150534 q = 1) : d151267 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d151267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29336 q ha hb
    | true =>
      simp only [d150534, d151267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94755 q = 1) (hb : d150535 q = 1) : d151268 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d151268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d151268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94756 q = 1) (hb : d150536 q = 1) : d151269 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94756, d150536, d151269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94756, d150536, d151269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94756 q = 1) (hb : d150537 q = 1) : d151270 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d151270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150537, d151270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94756 q = 1) (hb : d150538 q = 1) : d151271 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d151271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150538, d151271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d94756 q = 1) (hb : d150539 q = 1) : d151272 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d151272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150539, d151272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro29338 (p : Pattern) (ha : d94756 p = 1) (hb : d150545 p = 1) : d151278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94756 q = 1) (hb : d150540 q = 1) : d151273 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d151273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29337 q ha hb
    | true =>
      simp only [d150540, d151273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94756 q = 1) (hb : d150541 q = 1) : d151274 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d151274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d151274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94756 q = 1) (hb : d150542 q = 1) : d151275 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d151275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d151275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94756 q = 1) (hb : d150543 q = 1) : d151276 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d151276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d151276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94756 q = 1) (hb : d150544 q = 1) : d151277 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d151277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d151277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94756 q = 1) (hb : d150545 q = 1) : d151278 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d151278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d151278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29339 (p : Pattern) (ha : d94756 p = 1) (hb : d150551 p = 1) : d151284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94756 q = 1) (hb : d150546 q = 1) : d151279 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d151279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29338 q ha hb
    | true =>
      simp only [d150546, d151279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d94756 q = 1) (hb : d150547 q = 1) : d151280 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d151280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d151280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d94756 q = 1) (hb : d150548 q = 1) : d151281 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d151281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d151281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d94756 q = 1) (hb : d150549 q = 1) : d151282 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d151282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d151282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d94756 q = 1) (hb : d150550 q = 1) : d151283 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d151283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d151283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d94756 q = 1) (hb : d150551 q = 1) : d151284 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d151284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d151284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro29340 (p : Pattern) (ha : d1 p = 1) (hb : d151284 p = 1) : d151284 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d151284 q = 1) : d151284 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro29341 (p : Pattern) (ha : d0 p = 1) (hb : d151284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d151284 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro29342 (p : Pattern) (ha : d4818 p = 1) (hb : d146836 p = 1) : d148547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d116750 q = 1) : d20892 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4818 q = 1) (hb : d146836 q = 1) : d148547 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4818, d146836, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4818, d146836, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29343 (p : Pattern) (ha : d12227 p = 1) (hb : d146836 p = 1) : d151290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
    | true =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d146836 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12225 q = 1) (hb : d146836 q = 1) : d151288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12225, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d146836 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12226 q = 1) (hb : d146836 q = 1) : d151289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d151289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12226, d151289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12227 q = 1) (hb : d146836 q = 1) : d151290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d151290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12227, d151290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro29344 (p : Pattern) (ha : d12233 p = 1) (hb : d146836 p = 1) : d151296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d146836 q = 1) : d151295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12233 q = 1) (hb : d146836 q = 1) : d151296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d151296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d151296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29345 (p : Pattern) (ha : d115242 p = 1) (hb : d146836 p = 1) : d151302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d146836 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d146836 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12234 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
    | true =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115238 q = 1) (hb : d146836 q = 1) : d151298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115238, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146836 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115239 q = 1) (hb : d146836 q = 1) : d151299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115240 q = 1) (hb : d146836 q = 1) : d151300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115240, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115241 q = 1) (hb : d146836 q = 1) : d151301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115241, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115242 q = 1) (hb : d146836 q = 1) : d151302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d151302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115242, d151302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29346 (p : Pattern) (ha : d12240 p = 1) (hb : d146836 p = 1) : d151303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d146836 q = 1) : d151295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d151295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12240 q = 1) (hb : d146836 q = 1) : d151303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d151303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12240, d151303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29347 (p : Pattern) (ha : d115247 p = 1) (hb : d146836 p = 1) : d151309 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d146836 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d146836 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12234 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
    | true =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115238 q = 1) (hb : d146836 q = 1) : d151298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115238, d151298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146836 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115239 q = 1) (hb : d146836 q = 1) : d151299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d151299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115240 q = 1) (hb : d146836 q = 1) : d151300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115240, d151300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115241 q = 1) (hb : d146836 q = 1) : d151301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115241, d151301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d146836 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d146836 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12241 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29346 q ha hb
    | true =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115243 q = 1) (hb : d146836 q = 1) : d151305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115243, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d146836 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d115244 q = 1) (hb : d146836 q = 1) : d151306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115244, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115245 q = 1) (hb : d146836 q = 1) : d151307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d151307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115245, d151307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115246 q = 1) (hb : d146836 q = 1) : d151308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d151308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115246, d151308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d115247 q = 1) (hb : d146836 q = 1) : d151309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d151309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115247, d151309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro29348 (p : Pattern) (ha : d115254 p = 1) (hb : d146836 p = 1) : d151316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29346 q ha hb
    | true =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115243 q = 1) (hb : d146836 q = 1) : d151305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115243, d151305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d146836 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115244 q = 1) (hb : d146836 q = 1) : d151306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115244, d151306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115252 q = 1) (hb : d146836 q = 1) : d151314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d151314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115252, d151314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115253 q = 1) (hb : d146836 q = 1) : d151315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d151315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115253, d151315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115254 q = 1) (hb : d146836 q = 1) : d151316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d151316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115254, d151316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29349 (p : Pattern) (ha : d6078 p = 1) (hb : d146836 p = 1) : d148585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d116750 q = 1) : d20931 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6078 q = 1) (hb : d146836 q = 1) : d148585 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6078, d146836, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6078, d146836, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29350 (p : Pattern) (ha : d12261 p = 1) (hb : d146836 p = 1) : d151327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
    | true =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d146836 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12259 q = 1) (hb : d146836 q = 1) : d151325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12259, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d146836 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12260 q = 1) (hb : d146836 q = 1) : d151326 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d151326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12260, d151326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12261 q = 1) (hb : d146836 q = 1) : d151327 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d151327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12261, d151327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro29351 (p : Pattern) (ha : d12267 p = 1) (hb : d146836 p = 1) : d151333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d146836 q = 1) : d151328 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29350 q ha hb
    | true =>
      simp only [d12262, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d146836 q = 1) : d151329 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d146836 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12264 q = 1) (hb : d146836 q = 1) : d151330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d151330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d151330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12265 q = 1) (hb : d146836 q = 1) : d151331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d151331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12265, d151331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12266 q = 1) (hb : d146836 q = 1) : d151332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d151332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12266, d151332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12267 q = 1) (hb : d146836 q = 1) : d151333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d151333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12267, d151333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29352 (p : Pattern) (ha : d115264 p = 1) (hb : d146836 p = 1) : d151339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146836 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d146836 q = 1) : d151334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29351 q ha hb
    | true =>
      simp only [d12268, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115260 q = 1) (hb : d146836 q = 1) : d151335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d151335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115260, d151335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d146836 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115261 q = 1) (hb : d146836 q = 1) : d151336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d151336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115261, d151336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115262 q = 1) (hb : d146836 q = 1) : d151337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d151337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115262, d151337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115263 q = 1) (hb : d146836 q = 1) : d151338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d151338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115263, d151338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115264 q = 1) (hb : d146836 q = 1) : d151339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d151339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115264, d151339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29353 (p : Pattern) (ha : d115270 p = 1) (hb : d146836 p = 1) : d151345 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d146836 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115248 q = 1) (hb : d146836 q = 1) : d151310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d151310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29345 q ha hb
    | true =>
      simp only [d115248, d151310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29347 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d146836 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115249 q = 1) (hb : d146836 q = 1) : d151311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d151311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115249, d151311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115250 q = 1) (hb : d146836 q = 1) : d151312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d151312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115250, d151312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115251 q = 1) (hb : d146836 q = 1) : d151313 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d151313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115251, d151313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115255 q = 1) (hb : d146836 q = 1) : d151317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d151317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115255, d151317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29348 q ha hb
  have h8 (q : Pattern) (ha : d115256 q = 1) (hb : d146836 q = 1) : d151318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d151318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115256, d151318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d115257 q = 1) (hb : d146836 q = 1) : d151319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d151319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115257, d151319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d115258 q = 1) (hb : d146836 q = 1) : d151320 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d151320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115258, d151320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115259 q = 1) (hb : d146836 q = 1) : d151321 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d151321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115259, d151321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115265 q = 1) (hb : d146836 q = 1) : d151340 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d151340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115265, d151340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29352 q ha hb
  have h13 (q : Pattern) (ha : d115266 q = 1) (hb : d146836 q = 1) : d151341 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d151341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115266, d151341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d115267 q = 1) (hb : d146836 q = 1) : d151342 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d151342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115267, d151342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d115268 q = 1) (hb : d146836 q = 1) : d151343 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d151343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115268, d151343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d115269 q = 1) (hb : d146836 q = 1) : d151344 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d151344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115269, d151344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115270 q = 1) (hb : d146836 q = 1) : d151345 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d151345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115270, d151345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro29354 (p : Pattern) (ha : d12289 p = 1) (hb : d146836 p = 1) : d151355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
    | true =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d146836 q = 1) : d151351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d146836 q = 1) : d151352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d146836 q = 1) : d151353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d146836 q = 1) : d151354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12289 q = 1) (hb : d146836 q = 1) : d151355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29355 (p : Pattern) (ha : d12296 p = 1) (hb : d146836 p = 1) : d151362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
    | true =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d146836 q = 1) : d151351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d146836 q = 1) : d151352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d146836 q = 1) : d151353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d146836 q = 1) : d151354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12241 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29346 q ha hb
    | true =>
      simp only [d12241, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12292 q = 1) (hb : d146836 q = 1) : d151358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12293 q = 1) (hb : d146836 q = 1) : d151359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12293, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12294 q = 1) (hb : d146836 q = 1) : d151360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12295 q = 1) (hb : d146836 q = 1) : d151361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12296 q = 1) (hb : d146836 q = 1) : d151362 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12296, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro29356 (p : Pattern) (ha : d12373 p = 1) (hb : d146836 p = 1) : d151422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146836 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d146836 q = 1) : d151297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
    | true =>
      simp only [d12234, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d146836 q = 1) : d151351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d146836 q = 1) : d151352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d146836 q = 1) : d151353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d146836 q = 1) : d151354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d146836 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12373 q = 1) (hb : d146836 q = 1) : d151422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d151422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12373, d151422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29357 (p : Pattern) (ha : d12301 p = 1) (hb : d146836 p = 1) : d151367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d146836 q = 1) : d151366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12301 q = 1) (hb : d146836 q = 1) : d151367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d151367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d151367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29358 (p : Pattern) (ha : d12308 p = 1) (hb : d146836 p = 1) : d151374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d146836 q = 1) : d151372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d146836 q = 1) : d151373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12308 q = 1) (hb : d146836 q = 1) : d151374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d151374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d151374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29359 (p : Pattern) (ha : d12312 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12312 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12312, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29360 (p : Pattern) (ha : d12318 p = 1) (hb : d146836 p = 1) : d151383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d146836 q = 1) : d151378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29359 q ha hb
    | true =>
      simp only [d12313, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d146836 q = 1) : d151379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d146836 q = 1) : d151380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4819 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
    | true =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4820 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4821 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12316 q = 1) (hb : d146836 q = 1) : d151381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d146836 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12225 q = 1) (hb : d146836 q = 1) : d151288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12225, d151288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12317 q = 1) (hb : d146836 q = 1) : d151382 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d151382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12317, d151382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12318 q = 1) (hb : d146836 q = 1) : d151383 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d151383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12318, d151383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro29361 (p : Pattern) (ha : d12324 p = 1) (hb : d146836 p = 1) : d151389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d146836 q = 1) : d151384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29360 q ha hb
    | true =>
      simp only [d12319, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d146836 q = 1) : d151385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d146836 q = 1) : d151386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d146836 q = 1) : d151387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d146836 q = 1) : d151388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d146836 q = 1) : d151389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d151389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d151389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29362 (p : Pattern) (ha : d12344 p = 1) (hb : d146836 p = 1) : d151395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d146836 q = 1) : d151392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d146836 q = 1) : d151393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d146836 q = 1) : d151394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d146836 q = 1) : d151395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d151395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d151395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29363 (p : Pattern) (ha : d115280 p = 1) (hb : d146836 p = 1) : d151401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146836 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d146836 q = 1) : d151368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29357 q ha hb
    | true =>
      simp only [d12302, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d146836 q = 1) : d151369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d146836 q = 1) : d151370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d146836 q = 1) : d151371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146836 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d146836 q = 1) : d151375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29358 q ha hb
    | true =>
      simp only [d12309, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d146836 q = 1) : d151376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d146836 q = 1) : d151377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d146836 q = 1) : d151390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29361 q ha hb
    | true =>
      simp only [d12325, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
  have h11 (q : Pattern) (ha : d115276 q = 1) (hb : d146836 q = 1) : d151391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115276, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d146836 q = 1) : d151396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29362 q ha hb
    | true =>
      simp only [d12345, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d146836 q = 1) : d151397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115277 q = 1) (hb : d146836 q = 1) : d151398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115278 q = 1) (hb : d146836 q = 1) : d151399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115278, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115279 q = 1) (hb : d146836 q = 1) : d151400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115279, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115280 q = 1) (hb : d146836 q = 1) : d151401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d151401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d151401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro29364 (p : Pattern) (ha : d12351 p = 1) (hb : d146836 p = 1) : d151402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d146836 q = 1) : d151294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d151294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d146836 q = 1) : d151366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d151366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12351 q = 1) (hb : d146836 q = 1) : d151402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d151402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12351, d151402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29365 (p : Pattern) (ha : d12356 p = 1) (hb : d146836 p = 1) : d151407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146836 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d146836 q = 1) : d151293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d151293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d146836 q = 1) : d151372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d151372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d146836 q = 1) : d151373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d151373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12356 q = 1) (hb : d146836 q = 1) : d151407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d151407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12356, d151407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29366 (p : Pattern) (ha : d12360 p = 1) (hb : d146836 p = 1) : d151411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d146836 q = 1) : d151384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29360 q ha hb
    | true =>
      simp only [d12319, d151384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d146836 q = 1) : d151385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d151385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d146836 q = 1) : d151386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d151386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d146836 q = 1) : d151387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d151387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d146836 q = 1) : d151388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d151388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d146836 q = 1) : d151411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d151411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d151411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29367 (p : Pattern) (ha : d12365 p = 1) (hb : d146836 p = 1) : d151414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d146836 q = 1) : d151291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29343 q ha hb
    | true =>
      simp only [d12228, d151291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d146836 q = 1) : d151292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d151292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d146836 q = 1) : d151392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d151392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d146836 q = 1) : d151393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d151393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d146836 q = 1) : d151394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d151394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d146836 q = 1) : d151414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d151414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d151414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29368 (p : Pattern) (ha : d115285 p = 1) (hb : d146836 p = 1) : d151420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146836 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d146836 q = 1) : d151368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29357 q ha hb
    | true =>
      simp only [d12302, d151368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d146836 q = 1) : d151369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d151369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d146836 q = 1) : d151370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d151370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d146836 q = 1) : d151371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d151371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146836 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d146836 q = 1) : d151375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29358 q ha hb
    | true =>
      simp only [d12309, d151375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d146836 q = 1) : d151376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d151376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d146836 q = 1) : d151377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d151377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d146836 q = 1) : d151390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29361 q ha hb
    | true =>
      simp only [d12325, d151390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29344 q ha hb
  have h11 (q : Pattern) (ha : d115276 q = 1) (hb : d146836 q = 1) : d151391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115276, d151391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d146836 q = 1) : d151396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29362 q ha hb
    | true =>
      simp only [d12345, d151396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d146836 q = 1) : d151397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d151397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115277 q = 1) (hb : d146836 q = 1) : d151398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d151398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115278 q = 1) (hb : d146836 q = 1) : d151399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115278, d151399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115279 q = 1) (hb : d146836 q = 1) : d151400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115279, d151400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d146836 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12352 q = 1) (hb : d146836 q = 1) : d151403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d151403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29364 q ha hb
    | true =>
      simp only [d12352, d151403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12353 q = 1) (hb : d146836 q = 1) : d151404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d151404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d151404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12354 q = 1) (hb : d146836 q = 1) : d151405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d151405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12354, d151405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12355 q = 1) (hb : d146836 q = 1) : d151406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d151406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d151406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d146836 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12357 q = 1) (hb : d146836 q = 1) : d151408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d151408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29365 q ha hb
    | true =>
      simp only [d12357, d151408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12358 q = 1) (hb : d146836 q = 1) : d151409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d151409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d151409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12359 q = 1) (hb : d146836 q = 1) : d151410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d151410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12359, d151410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12361 q = 1) (hb : d146836 q = 1) : d151412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29366 q ha hb
    | true =>
      simp only [d12361, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29346 q ha hb
  have h27 (q : Pattern) (ha : d115281 q = 1) (hb : d146836 q = 1) : d151413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115281, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12366 q = 1) (hb : d146836 q = 1) : d151415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29367 q ha hb
    | true =>
      simp only [d12366, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12367 q = 1) (hb : d146836 q = 1) : d151416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12367, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115282 q = 1) (hb : d146836 q = 1) : d151417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115282, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115283 q = 1) (hb : d146836 q = 1) : d151418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d151418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115283, d151418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115284 q = 1) (hb : d146836 q = 1) : d151419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d151419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115284, d151419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115285 q = 1) (hb : d146836 q = 1) : d151420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d151420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115285, d151420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro29369 (p : Pattern) (ha : d115292 p = 1) (hb : d146836 p = 1) : d151429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d146836 q = 1) : d151412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29366 q ha hb
    | true =>
      simp only [d12361, d151412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29346 q ha hb
  have h2 (q : Pattern) (ha : d115281 q = 1) (hb : d146836 q = 1) : d151413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115281, d151413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d146836 q = 1) : d151415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29367 q ha hb
    | true =>
      simp only [d12366, d151415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d146836 q = 1) : d151416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d151416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d146836 q = 1) : d151417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d151417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d146836 q = 1) : d151427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d151427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d151427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d146836 q = 1) : d151428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d151428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d151428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d146836 q = 1) : d151429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d151429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d151429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29370 (p : Pattern) (ha : d12386 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12386 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12386, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29371 (p : Pattern) (ha : d12392 p = 1) (hb : d146836 p = 1) : d151440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d146836 q = 1) : d151435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29370 q ha hb
    | true =>
      simp only [d12387, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d146836 q = 1) : d151436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d146836 q = 1) : d151437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6079 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
    | true =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6080 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6081 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12390 q = 1) (hb : d146836 q = 1) : d151438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d146836 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12259 q = 1) (hb : d146836 q = 1) : d151325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12259, d151325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12391 q = 1) (hb : d146836 q = 1) : d151439 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d151439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12391, d151439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12392 q = 1) (hb : d146836 q = 1) : d151440 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d151440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12392, d151440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro29372 (p : Pattern) (ha : d12398 p = 1) (hb : d146836 p = 1) : d151446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d146836 q = 1) : d151441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d151441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29371 q ha hb
    | true =>
      simp only [d12393, d151441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d146836 q = 1) : d151442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d151442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d151442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d146836 q = 1) : d151328 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29350 q ha hb
    | true =>
      simp only [d12262, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d146836 q = 1) : d151329 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d146836 q = 1) : d151443 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d151443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d151443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d146836 q = 1) : d151444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d151444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d151444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d146836 q = 1) : d151445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d151445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d151445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d146836 q = 1) : d151446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d151446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d151446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29373 (p : Pattern) (ha : d12418 p = 1) (hb : d146836 p = 1) : d151452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d146836 q = 1) : d151328 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29350 q ha hb
    | true =>
      simp only [d12262, d151328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d146836 q = 1) : d151329 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d151329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d146836 q = 1) : d151449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d151449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d151449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d146836 q = 1) : d151450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d151450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d151450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d146836 q = 1) : d151451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d151451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d151451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d146836 q = 1) : d151452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d151452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d151452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29374 (p : Pattern) (ha : d115302 p = 1) (hb : d146836 p = 1) : d151458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d146836 q = 1) : d151447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d151447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29372 q ha hb
    | true =>
      simp only [d12399, d151447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29351 q ha hb
  have h2 (q : Pattern) (ha : d115298 q = 1) (hb : d146836 q = 1) : d151448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d151448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115298, d151448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d146836 q = 1) : d151453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d151453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29373 q ha hb
    | true =>
      simp only [d12419, d151453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d146836 q = 1) : d151454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d151454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d151454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d146836 q = 1) : d151455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d151455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d151455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d146836 q = 1) : d151456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d151456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d151456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d146836 q = 1) : d151457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d151457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d151457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d146836 q = 1) : d151458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d151458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d151458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29375 (p : Pattern) (ha : d115308 p = 1) (hb : d146836 p = 1) : d151464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d146836 q = 1) : d151356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d151356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d151356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29354 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d146836 q = 1) : d151357 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d151357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d151357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d146836 q = 1) : d151363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29354 q ha hb
    | true =>
      simp only [d12297, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29355 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d146836 q = 1) : d151364 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d146836 q = 1) : d151365 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d151365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d151365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115286 q = 1) (hb : d146836 q = 1) : d151421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d151421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29363 q ha hb
    | true =>
      simp only [d115286, d151421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29368 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d146836 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12374 q = 1) (hb : d146836 q = 1) : d151423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d151423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29356 q ha hb
    | true =>
      simp only [d12374, d151423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115287 q = 1) (hb : d146836 q = 1) : d151424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d151424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d151424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115288 q = 1) (hb : d146836 q = 1) : d151425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d151425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115288, d151425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115289 q = 1) (hb : d146836 q = 1) : d151426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d151426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115289, d151426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115293 q = 1) (hb : d146836 q = 1) : d151430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d151430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115293, d151430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29369 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d146836 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115294 q = 1) (hb : d146836 q = 1) : d151431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d151431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115294, d151431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115295 q = 1) (hb : d146836 q = 1) : d151432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d151432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115295, d151432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115296 q = 1) (hb : d146836 q = 1) : d151433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d151433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115296, d151433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115297 q = 1) (hb : d146836 q = 1) : d151434 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d151434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115297, d151434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115303 q = 1) (hb : d146836 q = 1) : d151459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d151459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115303, d151459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29374 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d146836 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115304 q = 1) (hb : d146836 q = 1) : d151460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d151460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115304, d151460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115305 q = 1) (hb : d146836 q = 1) : d151461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d151461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115305, d151461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115306 q = 1) (hb : d146836 q = 1) : d151462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d151462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115306, d151462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115307 q = 1) (hb : d146836 q = 1) : d151463 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d151463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115307, d151463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115308 q = 1) (hb : d146836 q = 1) : d151464 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d151464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115308, d151464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro29376 (p : Pattern) (ha : d115314 p = 1) (hb : d146836 p = 1) : d151470 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d146836 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115271 q = 1) (hb : d146836 q = 1) : d151346 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d151346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115271, d151346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29353 q ha hb
  have h3 (q : Pattern) (ha : d115272 q = 1) (hb : d146836 q = 1) : d151347 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d151347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115272, d151347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115273 q = 1) (hb : d146836 q = 1) : d151348 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d151348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115273, d151348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115274 q = 1) (hb : d146836 q = 1) : d151349 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d151349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115274, d151349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115275 q = 1) (hb : d146836 q = 1) : d151350 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d151350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115275, d151350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115309 q = 1) (hb : d146836 q = 1) : d151465 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d151465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d151465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29375 q ha hb
  have h8 (q : Pattern) (ha : d115310 q = 1) (hb : d146836 q = 1) : d151466 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d151466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d151466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115311 q = 1) (hb : d146836 q = 1) : d151467 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d151467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d151467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115312 q = 1) (hb : d146836 q = 1) : d151468 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d151468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d151468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115313 q = 1) (hb : d146836 q = 1) : d151469 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d151469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d151469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115314 q = 1) (hb : d146836 q = 1) : d151470 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d151470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115314, d151470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro29377 (p : Pattern) (ha : d12438 p = 1) (hb : d146836 p = 1) : d151473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d146836 q = 1) : d151378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29359 q ha hb
    | true =>
      simp only [d12313, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d146836 q = 1) : d151379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d146836 q = 1) : d151380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4819 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
    | true =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4820 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4821 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12316 q = 1) (hb : d146836 q = 1) : d151381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4822 q = 1) (hb : d146836 q = 1) : d151471 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4822, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12437 q = 1) (hb : d146836 q = 1) : d151472 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d151472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12437, d151472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12438 q = 1) (hb : d146836 q = 1) : d151473 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d151473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12438, d151473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro29378 (p : Pattern) (ha : d12442 p = 1) (hb : d146836 p = 1) : d151477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
    | true =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4822 q = 1) (hb : d146836 q = 1) : d151471 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4822, d151471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12441 q = 1) (hb : d146836 q = 1) : d151476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d151476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12441, d151476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12442 q = 1) (hb : d146836 q = 1) : d151477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d151477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12442, d151477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29379 (p : Pattern) (ha : d12448 p = 1) (hb : d146836 p = 1) : d151483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d146836 q = 1) : d151482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12448 q = 1) (hb : d146836 q = 1) : d151483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d151483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d151483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29380 (p : Pattern) (ha : d12452 p = 1) (hb : d146836 p = 1) : d151487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d146836 q = 1) : d151486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d146836 q = 1) : d151487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d151487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d151487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29381 (p : Pattern) (ha : d12458 p = 1) (hb : d146836 p = 1) : d151493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d146836 q = 1) : d151488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29379 q ha hb
    | true =>
      simp only [d12453, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29380 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d146836 q = 1) : d151489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d146836 q = 1) : d151490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d146836 q = 1) : d151491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d146836 q = 1) : d151492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12458 q = 1) (hb : d146836 q = 1) : d151493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29382 (p : Pattern) (ha : d12461 p = 1) (hb : d146836 p = 1) : d151496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d146836 q = 1) : d151482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d151482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12461 q = 1) (hb : d146836 q = 1) : d151496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d151496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12461, d151496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29383 (p : Pattern) (ha : d12462 p = 1) (hb : d146836 p = 1) : d151497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d146836 q = 1) : d151486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d151486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d146836 q = 1) : d151497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d151497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d151497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29384 (p : Pattern) (ha : d12468 p = 1) (hb : d146836 p = 1) : d151503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d146836 q = 1) : d151488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29379 q ha hb
    | true =>
      simp only [d12453, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29380 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d146836 q = 1) : d151489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d146836 q = 1) : d151490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d146836 q = 1) : d151491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d146836 q = 1) : d151492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12463 q = 1) (hb : d146836 q = 1) : d151498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29382 q ha hb
    | true =>
      simp only [d12463, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29383 q ha hb
  have h7 (q : Pattern) (ha : d12464 q = 1) (hb : d146836 q = 1) : d151499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12465 q = 1) (hb : d146836 q = 1) : d151500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12465, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12466 q = 1) (hb : d146836 q = 1) : d151501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12467 q = 1) (hb : d146836 q = 1) : d151502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12468 q = 1) (hb : d146836 q = 1) : d151503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12468, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29385 (p : Pattern) (ha : d12574 p = 1) (hb : d146836 p = 1) : d151579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d146836 q = 1) : d151488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29379 q ha hb
    | true =>
      simp only [d12453, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29380 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d146836 q = 1) : d151489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d146836 q = 1) : d151490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d146836 q = 1) : d151491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d146836 q = 1) : d151492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d146836 q = 1) : d151574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29380 q ha hb
    | true =>
      simp only [d12569, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d146836 q = 1) : d151575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d146836 q = 1) : d151576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d146836 q = 1) : d151577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d146836 q = 1) : d151578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12574 q = 1) (hb : d146836 q = 1) : d151579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d151579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12574, d151579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29386 (p : Pattern) (ha : d12580 p = 1) (hb : d146836 p = 1) : d151585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d146836 q = 1) : d151574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29380 q ha hb
    | true =>
      simp only [d12569, d151574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d146836 q = 1) : d151575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d151575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d146836 q = 1) : d151576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d151576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d146836 q = 1) : d151577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d151577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d146836 q = 1) : d151578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d151578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d146836 q = 1) : d151580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29383 q ha hb
    | true =>
      simp only [d12575, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d146836 q = 1) : d151581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d146836 q = 1) : d151582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d146836 q = 1) : d151583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d146836 q = 1) : d151584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d146836 q = 1) : d151585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d151585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d151585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29387 (p : Pattern) (ha : d12589 p = 1) (hb : d146836 p = 1) : d151594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d146836 q = 1) : d151580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29383 q ha hb
    | true =>
      simp only [d12575, d151580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d146836 q = 1) : d151581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d151581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d146836 q = 1) : d151582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d151582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d146836 q = 1) : d151583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d151583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d146836 q = 1) : d151584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d151584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d146836 q = 1) : d151594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d151594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d151594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29388 (p : Pattern) (ha : d12622 p = 1) (hb : d146836 p = 1) : d151622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
    | true =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6082 q = 1) (hb : d146836 q = 1) : d151612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6082, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12621 q = 1) (hb : d146836 q = 1) : d151621 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d151621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12621, d151621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12622 q = 1) (hb : d146836 q = 1) : d151622 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d151622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12622, d151622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29389 (p : Pattern) (ha : d12668 p = 1) (hb : d146836 p = 1) : d151645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d146836 q = 1) : d151623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29388 q ha hb
    | true =>
      simp only [d12623, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d146836 q = 1) : d151624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d146836 q = 1) : d151642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d151642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d151642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d146836 q = 1) : d151643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d151643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d151643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d146836 q = 1) : d151644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d151644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d151644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d146836 q = 1) : d151645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d151645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d151645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29390 (p : Pattern) (ha : d12674 p = 1) (hb : d146836 p = 1) : d151651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d146836 q = 1) : d151646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d151646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29389 q ha hb
    | true =>
      simp only [d12669, d151646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d146836 q = 1) : d151647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d151647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d151647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d146836 q = 1) : d151648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d151648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d151648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d146836 q = 1) : d151649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d151649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d151649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d146836 q = 1) : d151650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d151650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d151650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d146836 q = 1) : d151651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d151651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d151651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29391 (p : Pattern) (ha : d12473 p = 1) (hb : d146836 p = 1) : d151508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d146836 q = 1) : d151507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12473 q = 1) (hb : d146836 q = 1) : d151508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d151508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d151508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29392 (p : Pattern) (ha : d12475 p = 1) (hb : d146836 p = 1) : d151510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d146836 q = 1) : d151509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d146836 q = 1) : d151510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d151510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d151510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29393 (p : Pattern) (ha : d12482 p = 1) (hb : d146836 p = 1) : d151517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d146836 q = 1) : d151515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d146836 q = 1) : d151516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12482 q = 1) (hb : d146836 q = 1) : d151517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d151517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d151517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29394 (p : Pattern) (ha : d12485 p = 1) (hb : d146836 p = 1) : d151520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d146836 q = 1) : d151518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d146836 q = 1) : d151519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d146836 q = 1) : d151520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d151520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d151520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29395 (p : Pattern) (ha : d12489 p = 1) (hb : d146836 p = 1) : d148790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12489 q = 1) (hb : d146836 q = 1) : d148790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12489, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29396 (p : Pattern) (ha : d9381 p = 1) (hb : d116750 p = 1) : d5450 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5449 q = 1) : d5449 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9381 q = 1) (hb : d116750 q = 1) : d5450 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d116750, d5450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9381, d116750, d5450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29397 (p : Pattern) (ha : d12496 p = 1) (hb : d146836 p = 1) : d151527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d116750 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d116750 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d116750 q = 1) : d20995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d20995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d20995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12496 q = 1) (hb : d146836 q = 1) : d151527 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12496, d146836, d151527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12496, d146836, d151527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29398 (p : Pattern) (ha : d12502 p = 1) (hb : d146836 p = 1) : d151533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d146836 q = 1) : d151524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29395 q ha hb
    | true =>
      simp only [d12490, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29359 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d146836 q = 1) : d151525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d146836 q = 1) : d151526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12497 q = 1) (hb : d146836 q = 1) : d151528 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d151528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29359 q ha hb
    | true =>
      simp only [d12497, d151528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29397 q ha hb
  have h5 (q : Pattern) (ha : d12498 q = 1) (hb : d146836 q = 1) : d151529 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d151529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12498, d151529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12499 q = 1) (hb : d146836 q = 1) : d151530 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d151530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12499, d151530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12500 q = 1) (hb : d146836 q = 1) : d151531 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d151531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12500, d151531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12313 q = 1) (hb : d146836 q = 1) : d151378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29359 q ha hb
    | true =>
      simp only [d12313, d151378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
  have h9 (q : Pattern) (ha : d12314 q = 1) (hb : d146836 q = 1) : d151379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d151379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12315 q = 1) (hb : d146836 q = 1) : d151380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d151380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d146836 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4819 q = 1) (hb : d146836 q = 1) : d151285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29342 q ha hb
    | true =>
      simp only [d4819, d151285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4820 q = 1) (hb : d146836 q = 1) : d151286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d151286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4821 q = 1) (hb : d146836 q = 1) : d151287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d151287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12316 q = 1) (hb : d146836 q = 1) : d151381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12316, d151381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12501 q = 1) (hb : d146836 q = 1) : d151532 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d151532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12501, d151532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12502 q = 1) (hb : d146836 q = 1) : d151533 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d151533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12502, d151533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro29399 (p : Pattern) (ha : d12508 p = 1) (hb : d146836 p = 1) : d151539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d146836 q = 1) : d151534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29398 q ha hb
    | true =>
      simp only [d12503, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d146836 q = 1) : d151535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d146836 q = 1) : d151536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d146836 q = 1) : d151537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d146836 q = 1) : d151538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d146836 q = 1) : d151539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d151539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d151539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29400 (p : Pattern) (ha : d12537 p = 1) (hb : d146836 p = 1) : d151545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d146836 q = 1) : d151542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d146836 q = 1) : d151543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d146836 q = 1) : d151544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d146836 q = 1) : d151545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d151545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d151545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29401 (p : Pattern) (ha : d115319 p = 1) (hb : d146836 p = 1) : d151551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d146836 q = 1) : d151511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29391 q ha hb
    | true =>
      simp only [d12476, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29392 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d146836 q = 1) : d151512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d146836 q = 1) : d151513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d146836 q = 1) : d151514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d146836 q = 1) : d151521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29393 q ha hb
    | true =>
      simp only [d12486, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29394 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d146836 q = 1) : d151522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d146836 q = 1) : d151523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d146836 q = 1) : d151540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29399 q ha hb
    | true =>
      simp only [d12509, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29379 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d146836 q = 1) : d151541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d146836 q = 1) : d151546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29400 q ha hb
    | true =>
      simp only [d12538, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d146836 q = 1) : d151547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d146836 q = 1) : d151548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d146836 q = 1) : d151549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d146836 q = 1) : d151550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115319 q = 1) (hb : d146836 q = 1) : d151551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d151551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d151551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29402 (p : Pattern) (ha : d12544 p = 1) (hb : d146836 p = 1) : d151552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d146836 q = 1) : d151481 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d151481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d146836 q = 1) : d151507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d151507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12544 q = 1) (hb : d146836 q = 1) : d151552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d151552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12544, d151552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29403 (p : Pattern) (ha : d12545 p = 1) (hb : d146836 p = 1) : d151553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d146836 q = 1) : d151485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d151485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d146836 q = 1) : d151509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d151509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d146836 q = 1) : d151553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d151553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d151553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29404 (p : Pattern) (ha : d12550 p = 1) (hb : d146836 p = 1) : d151558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d146836 q = 1) : d151480 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d151480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d146836 q = 1) : d151515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d151515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d146836 q = 1) : d151516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d151516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12550 q = 1) (hb : d146836 q = 1) : d151558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d151558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12550, d151558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29405 (p : Pattern) (ha : d12551 p = 1) (hb : d146836 p = 1) : d151559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d146836 q = 1) : d151478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29378 q ha hb
    | true =>
      simp only [d12443, d151478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d146836 q = 1) : d151479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d151479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d146836 q = 1) : d151484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d151484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d146836 q = 1) : d151518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d151518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d146836 q = 1) : d151519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d151519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d146836 q = 1) : d151559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d151559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d151559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29406 (p : Pattern) (ha : d12555 p = 1) (hb : d146836 p = 1) : d151563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d146836 q = 1) : d151534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29398 q ha hb
    | true =>
      simp only [d12503, d151534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d146836 q = 1) : d151535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d151535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d146836 q = 1) : d151536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d151536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d146836 q = 1) : d151537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d151537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d146836 q = 1) : d151538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d151538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d146836 q = 1) : d151563 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d151563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d151563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29407 (p : Pattern) (ha : d12561 p = 1) (hb : d146836 p = 1) : d151566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d146836 q = 1) : d151474 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29377 q ha hb
    | true =>
      simp only [d12439, d151474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d146836 q = 1) : d151475 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d151475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d146836 q = 1) : d151542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d151542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d146836 q = 1) : d151543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d151543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d146836 q = 1) : d151544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d151544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d146836 q = 1) : d151566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d151566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d151566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29408 (p : Pattern) (ha : d115324 p = 1) (hb : d146836 p = 1) : d151572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d146836 q = 1) : d151511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29391 q ha hb
    | true =>
      simp only [d12476, d151511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29392 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d146836 q = 1) : d151512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d151512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d146836 q = 1) : d151513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d151513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d146836 q = 1) : d151514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d151514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d146836 q = 1) : d151521 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29393 q ha hb
    | true =>
      simp only [d12486, d151521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29394 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d146836 q = 1) : d151522 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d151522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d146836 q = 1) : d151523 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d151523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d146836 q = 1) : d151540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29399 q ha hb
    | true =>
      simp only [d12509, d151540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29379 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d146836 q = 1) : d151541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d151541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d146836 q = 1) : d151546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29400 q ha hb
    | true =>
      simp only [d12538, d151546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d146836 q = 1) : d151547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d151547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d146836 q = 1) : d151548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d151548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d146836 q = 1) : d151549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d151549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d146836 q = 1) : d151550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d151550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12546 q = 1) (hb : d146836 q = 1) : d151554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d151554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29402 q ha hb
    | true =>
      simp only [d12546, d151554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29403 q ha hb
  have h16 (q : Pattern) (ha : d12547 q = 1) (hb : d146836 q = 1) : d151555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d151555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d151555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12548 q = 1) (hb : d146836 q = 1) : d151556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d151556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12548, d151556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12549 q = 1) (hb : d146836 q = 1) : d151557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d151557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d151557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12552 q = 1) (hb : d146836 q = 1) : d151560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d151560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29404 q ha hb
    | true =>
      simp only [d12552, d151560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29405 q ha hb
  have h20 (q : Pattern) (ha : d12553 q = 1) (hb : d146836 q = 1) : d151561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d151561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d151561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12554 q = 1) (hb : d146836 q = 1) : d151562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d151562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12554, d151562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12556 q = 1) (hb : d146836 q = 1) : d151564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29406 q ha hb
    | true =>
      simp only [d12556, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29382 q ha hb
  have h23 (q : Pattern) (ha : d115320 q = 1) (hb : d146836 q = 1) : d151565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115320, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12562 q = 1) (hb : d146836 q = 1) : d151567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29407 q ha hb
    | true =>
      simp only [d12562, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12563 q = 1) (hb : d146836 q = 1) : d151568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12563, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115321 q = 1) (hb : d146836 q = 1) : d151569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115321, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115322 q = 1) (hb : d146836 q = 1) : d151570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d151570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115322, d151570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115323 q = 1) (hb : d146836 q = 1) : d151571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d151571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115323, d151571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115324 q = 1) (hb : d146836 q = 1) : d151572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d151572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115324, d151572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29409 (p : Pattern) (ha : d115331 p = 1) (hb : d146836 p = 1) : d151592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d146836 q = 1) : d151564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29406 q ha hb
    | true =>
      simp only [d12556, d151564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29382 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d146836 q = 1) : d151565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d151565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d146836 q = 1) : d151567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29407 q ha hb
    | true =>
      simp only [d12562, d151567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d146836 q = 1) : d151568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d151568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d146836 q = 1) : d151569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d151569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d146836 q = 1) : d151590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d151590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d151590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d146836 q = 1) : d151591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d151591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d151591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d146836 q = 1) : d151592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d151592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d151592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29410 (p : Pattern) (ha : d12595 p = 1) (hb : d146836 p = 1) : d148863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12595 q = 1) (hb : d146836 q = 1) : d148863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12595, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29411 (p : Pattern) (ha : d12604 p = 1) (hb : d146836 p = 1) : d151603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d116750 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d116750 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d116750 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d116750 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d116750 q = 1) : d21076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d21076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d21076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12604 q = 1) (hb : d146836 q = 1) : d151603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12604, d146836, d151603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12604, d146836, d151603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29412 (p : Pattern) (ha : d12610 p = 1) (hb : d146836 p = 1) : d151609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d146836 q = 1) : d151600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29410 q ha hb
    | true =>
      simp only [d12596, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29370 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d146836 q = 1) : d151601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d146836 q = 1) : d151602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12605 q = 1) (hb : d146836 q = 1) : d151604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d151604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29370 q ha hb
    | true =>
      simp only [d12605, d151604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29411 q ha hb
  have h5 (q : Pattern) (ha : d12606 q = 1) (hb : d146836 q = 1) : d151605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d151605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12606, d151605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12607 q = 1) (hb : d146836 q = 1) : d151606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d151606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12607, d151606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12608 q = 1) (hb : d146836 q = 1) : d151607 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d151607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12608, d151607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12387 q = 1) (hb : d146836 q = 1) : d151435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29370 q ha hb
    | true =>
      simp only [d12387, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
  have h9 (q : Pattern) (ha : d12388 q = 1) (hb : d146836 q = 1) : d151436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12389 q = 1) (hb : d146836 q = 1) : d151437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6079 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
    | true =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6080 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6081 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12390 q = 1) (hb : d146836 q = 1) : d151438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12390, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12609 q = 1) (hb : d146836 q = 1) : d151608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d151608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12609, d151608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12610 q = 1) (hb : d146836 q = 1) : d151609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d151609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12610, d151609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro29413 (p : Pattern) (ha : d12614 p = 1) (hb : d146836 p = 1) : d151614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d146836 q = 1) : d151435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29370 q ha hb
    | true =>
      simp only [d12387, d151435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d146836 q = 1) : d151436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d151436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d146836 q = 1) : d151437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d151437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d146836 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6079 q = 1) (hb : d146836 q = 1) : d151322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29349 q ha hb
    | true =>
      simp only [d6079, d151322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6080 q = 1) (hb : d146836 q = 1) : d151323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d151323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6081 q = 1) (hb : d146836 q = 1) : d151324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d151324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12390 q = 1) (hb : d146836 q = 1) : d151438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d151438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6082 q = 1) (hb : d146836 q = 1) : d151612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6082, d151612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12613 q = 1) (hb : d146836 q = 1) : d151613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d151613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12613, d151613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12614 q = 1) (hb : d146836 q = 1) : d151614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d151614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12614, d151614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro29414 (p : Pattern) (ha : d12620 p = 1) (hb : d146836 p = 1) : d151620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d146836 q = 1) : d151610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d151610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29412 q ha hb
    | true =>
      simp only [d12611, d151610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d146836 q = 1) : d151611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d151611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d151611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d146836 q = 1) : d151615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29413 q ha hb
    | true =>
      simp only [d12615, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d146836 q = 1) : d151616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d146836 q = 1) : d151617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d151617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d151617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d146836 q = 1) : d151618 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d151618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d151618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d146836 q = 1) : d151619 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d151619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d151619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d146836 q = 1) : d151620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d151620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d151620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29415 (p : Pattern) (ha : d12628 p = 1) (hb : d146836 p = 1) : d151628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d146836 q = 1) : d151615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29413 q ha hb
    | true =>
      simp only [d12615, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d146836 q = 1) : d151616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d146836 q = 1) : d151623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29388 q ha hb
    | true =>
      simp only [d12623, d151623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d146836 q = 1) : d151624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d151624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12625 q = 1) (hb : d146836 q = 1) : d151625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d151625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d151625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12626 q = 1) (hb : d146836 q = 1) : d151626 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d151626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12626, d151626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12627 q = 1) (hb : d146836 q = 1) : d151627 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d151627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12627, d151627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12628 q = 1) (hb : d146836 q = 1) : d151628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d151628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12628, d151628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29416 (p : Pattern) (ha : d12657 p = 1) (hb : d146836 p = 1) : d151634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d146836 q = 1) : d151615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29413 q ha hb
    | true =>
      simp only [d12615, d151615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d146836 q = 1) : d151616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d151616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d146836 q = 1) : d151631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d151631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d151631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d146836 q = 1) : d151632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d151632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d151632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d146836 q = 1) : d151633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d151633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d151633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d146836 q = 1) : d151634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d151634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d151634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29417 (p : Pattern) (ha : d115341 p = 1) (hb : d146836 p = 1) : d151640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d146836 q = 1) : d151629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d151629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29414 q ha hb
    | true =>
      simp only [d12629, d151629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29415 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d146836 q = 1) : d151630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d151630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d151630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d146836 q = 1) : d151635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d151635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29416 q ha hb
    | true =>
      simp only [d12658, d151635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d146836 q = 1) : d151636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d151636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d151636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d146836 q = 1) : d151637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d151637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d151637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d146836 q = 1) : d151638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d151638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d151638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d146836 q = 1) : d151639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d151639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d151639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d146836 q = 1) : d151640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d151640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d151640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29418 (p : Pattern) (ha : d115347 p = 1) (hb : d146836 p = 1) : d151657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d146836 q = 1) : d151494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d151494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d151494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29381 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d146836 q = 1) : d151495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d151495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d151495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d146836 q = 1) : d151504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29381 q ha hb
    | true =>
      simp only [d12469, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29384 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d146836 q = 1) : d151505 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d146836 q = 1) : d151506 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d151506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d151506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d146836 q = 1) : d151573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d151573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29401 q ha hb
    | true =>
      simp only [d115325, d151573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29408 q ha hb
  have h7 (q : Pattern) (ha : d12581 q = 1) (hb : d146836 q = 1) : d151586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d151586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29385 q ha hb
    | true =>
      simp only [d12581, d151586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29386 q ha hb
  have h8 (q : Pattern) (ha : d115326 q = 1) (hb : d146836 q = 1) : d151587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d151587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d151587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115327 q = 1) (hb : d146836 q = 1) : d151588 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d151588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115327, d151588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115328 q = 1) (hb : d146836 q = 1) : d151589 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d151589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d151589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115332 q = 1) (hb : d146836 q = 1) : d151593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d151593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d151593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29409 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d146836 q = 1) : d151595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d151595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d151595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29387 q ha hb
  have h13 (q : Pattern) (ha : d115333 q = 1) (hb : d146836 q = 1) : d151596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d151596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115333, d151596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115334 q = 1) (hb : d146836 q = 1) : d151597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d151597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115334, d151597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115335 q = 1) (hb : d146836 q = 1) : d151598 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d151598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115335, d151598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115336 q = 1) (hb : d146836 q = 1) : d151599 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d151599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115336, d151599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115342 q = 1) (hb : d146836 q = 1) : d151641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d151641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d151641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29417 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d146836 q = 1) : d151652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d151652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d151652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29390 q ha hb
  have h19 (q : Pattern) (ha : d115343 q = 1) (hb : d146836 q = 1) : d151653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d151653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115343, d151653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115344 q = 1) (hb : d146836 q = 1) : d151654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d151654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115344, d151654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115345 q = 1) (hb : d146836 q = 1) : d151655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d151655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115345, d151655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115346 q = 1) (hb : d146836 q = 1) : d151656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d151656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115346, d151656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115347 q = 1) (hb : d146836 q = 1) : d151657 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d151657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115347, d151657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29419 (p : Pattern) (ha : d115353 p = 1) (hb : d146836 p = 1) : d151663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d146836 q = 1) : d151658 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d151658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d151658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29418 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d146836 q = 1) : d151659 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d151659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d151659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d146836 q = 1) : d151660 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d151660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d151660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d146836 q = 1) : d151661 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d151661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d151661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d146836 q = 1) : d151662 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d151662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d151662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d146836 q = 1) : d151663 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d151663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d151663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29420 (p : Pattern) (ha : d4913 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d755 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4913 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4913, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29421 (p : Pattern) (ha : d12693 p = 1) (hb : d146836 p = 1) : d151671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12688 q = 1) (hb : d146836 q = 1) : d151524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29395 q ha hb
    | true =>
      simp only [d12688, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29420 q ha hb
  have h2 (q : Pattern) (ha : d12689 q = 1) (hb : d146836 q = 1) : d151525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d146836 q = 1) : d151526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d146836 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4914 q = 1) (hb : d146836 q = 1) : d151665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29420 q ha hb
    | true =>
      simp only [d4914, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4915 q = 1) (hb : d146836 q = 1) : d151666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4916 q = 1) (hb : d146836 q = 1) : d151667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12691 q = 1) (hb : d146836 q = 1) : d151668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12691, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4917 q = 1) (hb : d146836 q = 1) : d151669 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4917, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12692 q = 1) (hb : d146836 q = 1) : d151670 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d151670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12692, d151670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12693 q = 1) (hb : d146836 q = 1) : d151671 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d151671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12693, d151671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro29422 (p : Pattern) (ha : d12697 p = 1) (hb : d146836 p = 1) : d151675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d146836 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4914 q = 1) (hb : d146836 q = 1) : d151665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29420 q ha hb
    | true =>
      simp only [d4914, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4915 q = 1) (hb : d146836 q = 1) : d151666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4916 q = 1) (hb : d146836 q = 1) : d151667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4917 q = 1) (hb : d146836 q = 1) : d151669 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4917, d151669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12696 q = 1) (hb : d146836 q = 1) : d151674 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d151674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12696, d151674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12697 q = 1) (hb : d146836 q = 1) : d151675 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d151675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12697, d151675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29423 (p : Pattern) (ha : d12703 p = 1) (hb : d146836 p = 1) : d151681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d146836 q = 1) : d151680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12703 q = 1) (hb : d146836 q = 1) : d151681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d151681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d151681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29424 (p : Pattern) (ha : d12707 p = 1) (hb : d146836 p = 1) : d151685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d146836 q = 1) : d151684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d146836 q = 1) : d151685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d151685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d151685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29425 (p : Pattern) (ha : d12713 p = 1) (hb : d146836 p = 1) : d151691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d146836 q = 1) : d151686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29423 q ha hb
    | true =>
      simp only [d12708, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29424 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d146836 q = 1) : d151687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d146836 q = 1) : d151688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d146836 q = 1) : d151689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d146836 q = 1) : d151690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12713 q = 1) (hb : d146836 q = 1) : d151691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29426 (p : Pattern) (ha : d12716 p = 1) (hb : d146836 p = 1) : d151694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d146836 q = 1) : d151680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d151680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12716 q = 1) (hb : d146836 q = 1) : d151694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d151694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12716, d151694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29427 (p : Pattern) (ha : d12717 p = 1) (hb : d146836 p = 1) : d151695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d146836 q = 1) : d151684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d151684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d146836 q = 1) : d151695 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d151695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d151695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29428 (p : Pattern) (ha : d12723 p = 1) (hb : d146836 p = 1) : d151701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d146836 q = 1) : d151686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29423 q ha hb
    | true =>
      simp only [d12708, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29424 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d146836 q = 1) : d151687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d146836 q = 1) : d151688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d146836 q = 1) : d151689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d146836 q = 1) : d151690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12718 q = 1) (hb : d146836 q = 1) : d151696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29426 q ha hb
    | true =>
      simp only [d12718, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29427 q ha hb
  have h7 (q : Pattern) (ha : d12719 q = 1) (hb : d146836 q = 1) : d151697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12720 q = 1) (hb : d146836 q = 1) : d151698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12720, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12721 q = 1) (hb : d146836 q = 1) : d151699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12722 q = 1) (hb : d146836 q = 1) : d151700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12723 q = 1) (hb : d146836 q = 1) : d151701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12723, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29429 (p : Pattern) (ha : d12833 p = 1) (hb : d146836 p = 1) : d151777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d146836 q = 1) : d151686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29423 q ha hb
    | true =>
      simp only [d12708, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29424 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d146836 q = 1) : d151687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d146836 q = 1) : d151688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d146836 q = 1) : d151689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d146836 q = 1) : d151690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d146836 q = 1) : d151772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29424 q ha hb
    | true =>
      simp only [d12828, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d146836 q = 1) : d151773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d146836 q = 1) : d151774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d146836 q = 1) : d151775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d146836 q = 1) : d151776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12833 q = 1) (hb : d146836 q = 1) : d151777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d151777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12833, d151777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29430 (p : Pattern) (ha : d12839 p = 1) (hb : d146836 p = 1) : d151783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d146836 q = 1) : d151772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29424 q ha hb
    | true =>
      simp only [d12828, d151772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d146836 q = 1) : d151773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d151773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d146836 q = 1) : d151774 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d151774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d146836 q = 1) : d151775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d151775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d146836 q = 1) : d151776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d151776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d146836 q = 1) : d151778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29427 q ha hb
    | true =>
      simp only [d12834, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d146836 q = 1) : d151779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d146836 q = 1) : d151780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d146836 q = 1) : d151781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d146836 q = 1) : d151782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d146836 q = 1) : d151783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d151783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d151783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29431 (p : Pattern) (ha : d12848 p = 1) (hb : d146836 p = 1) : d151792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d146836 q = 1) : d151778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29427 q ha hb
    | true =>
      simp only [d12834, d151778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d146836 q = 1) : d151779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d151779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d146836 q = 1) : d151780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d151780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d146836 q = 1) : d151781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d151781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d146836 q = 1) : d151782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d151782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d146836 q = 1) : d151792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d151792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d151792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29432 (p : Pattern) (ha : d6210 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d975 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6210 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6210, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29433 (p : Pattern) (ha : d12885 p = 1) (hb : d146836 p = 1) : d151824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d146836 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6211 q = 1) (hb : d146836 q = 1) : d151806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29432 q ha hb
    | true =>
      simp only [d6211, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6212 q = 1) (hb : d146836 q = 1) : d151807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6213 q = 1) (hb : d146836 q = 1) : d151808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6214 q = 1) (hb : d146836 q = 1) : d151814 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6214, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12884 q = 1) (hb : d146836 q = 1) : d151823 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, d151823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12884, d151823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12885 q = 1) (hb : d146836 q = 1) : d151824 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, d151824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12885, d151824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro29434 (p : Pattern) (ha : d12935 p = 1) (hb : d146836 p = 1) : d151847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d146836 q = 1) : d151825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29433 q ha hb
    | true =>
      simp only [d12886, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d146836 q = 1) : d151826 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d146836 q = 1) : d151844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, d151844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, d151844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d146836 q = 1) : d151845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, d151845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, d151845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d146836 q = 1) : d151846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, d151846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, d151846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d146836 q = 1) : d151847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, d151847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, d151847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29435 (p : Pattern) (ha : d12941 p = 1) (hb : d146836 p = 1) : d151853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d146836 q = 1) : d151848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, d151848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29434 q ha hb
    | true =>
      simp only [d12936, d151848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d146836 q = 1) : d151849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, d151849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, d151849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d146836 q = 1) : d151850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, d151850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, d151850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d146836 q = 1) : d151851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, d151851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, d151851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d146836 q = 1) : d151852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, d151852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, d151852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d146836 q = 1) : d151853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, d151853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, d151853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29436 (p : Pattern) (ha : d12728 p = 1) (hb : d146836 p = 1) : d151706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d146836 q = 1) : d151705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12728 q = 1) (hb : d146836 q = 1) : d151706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d151706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d151706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29437 (p : Pattern) (ha : d12730 p = 1) (hb : d146836 p = 1) : d151708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d146836 q = 1) : d151707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d146836 q = 1) : d151708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, d151708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, d151708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29438 (p : Pattern) (ha : d12737 p = 1) (hb : d146836 p = 1) : d151715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d146836 q = 1) : d151713 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d146836 q = 1) : d151714 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12737 q = 1) (hb : d146836 q = 1) : d151715 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d151715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d151715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29439 (p : Pattern) (ha : d12740 p = 1) (hb : d146836 p = 1) : d151718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d146836 q = 1) : d151716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d146836 q = 1) : d151717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d146836 q = 1) : d151718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, d151718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, d151718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29440 (p : Pattern) (ha : d12744 p = 1) (hb : d146836 p = 1) : d148978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d116750 q = 1) : d21482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
    | true =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d116750 q = 1) : d21483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d116750 q = 1) : d21484 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d21484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d21484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d116750 q = 1) : d21485 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d21485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d21485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d838 q = 1) (hb : d116750 q = 1) : d21486 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d21486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d838, d21486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12744 q = 1) (hb : d146836 q = 1) : d148978 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12744, d146836, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12744, d146836, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29441 (p : Pattern) (ha : d9467 p = 1) (hb : d116750 p = 1) : d21188 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d9466 q = 1) : d9466 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9467 q = 1) (hb : d116750 q = 1) : d21188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9467, d116750, d21188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9467, d116750, d21188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29442 (p : Pattern) (ha : d12751 p = 1) (hb : d146836 p = 1) : d151725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d116750 q = 1) : d21191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12750 q = 1) (hb : d116750 q = 1) : d21418 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d21418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d21418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12751 q = 1) (hb : d146836 q = 1) : d151725 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12751, d146836, d151725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12751, d146836, d151725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29443 (p : Pattern) (ha : d12757 p = 1) (hb : d146836 p = 1) : d151731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d146836 q = 1) : d151722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d151722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29440 q ha hb
    | true =>
      simp only [d12745, d151722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29395 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d146836 q = 1) : d151723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d151723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d151723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d146836 q = 1) : d151724 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d151724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d151724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12752 q = 1) (hb : d146836 q = 1) : d151726 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d151726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29395 q ha hb
    | true =>
      simp only [d12752, d151726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29442 q ha hb
  have h5 (q : Pattern) (ha : d12753 q = 1) (hb : d146836 q = 1) : d151727 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d151727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12753, d151727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12754 q = 1) (hb : d146836 q = 1) : d151728 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d151728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12754, d151728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12755 q = 1) (hb : d146836 q = 1) : d151729 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d151729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12755, d151729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12688 q = 1) (hb : d146836 q = 1) : d151524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29395 q ha hb
    | true =>
      simp only [d12688, d151524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29420 q ha hb
  have h9 (q : Pattern) (ha : d12689 q = 1) (hb : d146836 q = 1) : d151525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d151525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12690 q = 1) (hb : d146836 q = 1) : d151526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d151526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d146836 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4914 q = 1) (hb : d146836 q = 1) : d151665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29420 q ha hb
    | true =>
      simp only [d4914, d151665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4915 q = 1) (hb : d146836 q = 1) : d151666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d151666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4916 q = 1) (hb : d146836 q = 1) : d151667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d151667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12691 q = 1) (hb : d146836 q = 1) : d151668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12691, d151668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12756 q = 1) (hb : d146836 q = 1) : d151730 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d151730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12756, d151730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12757 q = 1) (hb : d146836 q = 1) : d151731 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d151731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12757, d151731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro29444 (p : Pattern) (ha : d12763 p = 1) (hb : d146836 p = 1) : d151737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d146836 q = 1) : d151732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29443 q ha hb
    | true =>
      simp only [d12758, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d146836 q = 1) : d151733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d146836 q = 1) : d151734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d146836 q = 1) : d151735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d146836 q = 1) : d151736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d146836 q = 1) : d151737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d151737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d151737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29445 (p : Pattern) (ha : d12796 p = 1) (hb : d146836 p = 1) : d151743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d146836 q = 1) : d151740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d146836 q = 1) : d151741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d146836 q = 1) : d151742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d146836 q = 1) : d151743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d151743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d151743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29446 (p : Pattern) (ha : d115359 p = 1) (hb : d146836 p = 1) : d151749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d146836 q = 1) : d151709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29436 q ha hb
    | true =>
      simp only [d12731, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29437 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d146836 q = 1) : d151710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d146836 q = 1) : d151711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d146836 q = 1) : d151712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d146836 q = 1) : d151719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29438 q ha hb
    | true =>
      simp only [d12741, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29439 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d146836 q = 1) : d151720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d146836 q = 1) : d151721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d146836 q = 1) : d151738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29444 q ha hb
    | true =>
      simp only [d12764, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29423 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d146836 q = 1) : d151739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d146836 q = 1) : d151744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29445 q ha hb
    | true =>
      simp only [d12797, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d146836 q = 1) : d151745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d146836 q = 1) : d151746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d146836 q = 1) : d151747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d146836 q = 1) : d151748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115359 q = 1) (hb : d146836 q = 1) : d151749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d151749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d151749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29447 (p : Pattern) (ha : d12803 p = 1) (hb : d146836 p = 1) : d151750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d146836 q = 1) : d151679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d151679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d146836 q = 1) : d151705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d151705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12803 q = 1) (hb : d146836 q = 1) : d151750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d151750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12803, d151750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29448 (p : Pattern) (ha : d12804 p = 1) (hb : d146836 p = 1) : d151751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d146836 q = 1) : d151683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d151683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d146836 q = 1) : d151707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d151707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d146836 q = 1) : d151751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, d151751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, d151751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29449 (p : Pattern) (ha : d12809 p = 1) (hb : d146836 p = 1) : d151756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d146836 q = 1) : d151678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d151678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d146836 q = 1) : d151713 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d151713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d146836 q = 1) : d151714 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d151714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12809 q = 1) (hb : d146836 q = 1) : d151756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d151756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12809, d151756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29450 (p : Pattern) (ha : d12810 p = 1) (hb : d146836 p = 1) : d151757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d146836 q = 1) : d151676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29422 q ha hb
    | true =>
      simp only [d12698, d151676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d146836 q = 1) : d151677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d151677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d146836 q = 1) : d151682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d151682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d146836 q = 1) : d151716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d151716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d146836 q = 1) : d151717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d151717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d146836 q = 1) : d151757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, d151757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, d151757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29451 (p : Pattern) (ha : d12814 p = 1) (hb : d146836 p = 1) : d151761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d146836 q = 1) : d151732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29443 q ha hb
    | true =>
      simp only [d12758, d151732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d146836 q = 1) : d151733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d151733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d146836 q = 1) : d151734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d151734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d146836 q = 1) : d151735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d151735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d146836 q = 1) : d151736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d151736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d146836 q = 1) : d151761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d151761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d151761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29452 (p : Pattern) (ha : d12820 p = 1) (hb : d146836 p = 1) : d151764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d146836 q = 1) : d151672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29421 q ha hb
    | true =>
      simp only [d12694, d151672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d146836 q = 1) : d151673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d151673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d146836 q = 1) : d151740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d151740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d146836 q = 1) : d151741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d151741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d146836 q = 1) : d151742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d151742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d146836 q = 1) : d151764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d151764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d151764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29453 (p : Pattern) (ha : d115364 p = 1) (hb : d146836 p = 1) : d151770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d146836 q = 1) : d151709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29436 q ha hb
    | true =>
      simp only [d12731, d151709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29437 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d146836 q = 1) : d151710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d151710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d146836 q = 1) : d151711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d151711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d146836 q = 1) : d151712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d151712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d146836 q = 1) : d151719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29438 q ha hb
    | true =>
      simp only [d12741, d151719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29439 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d146836 q = 1) : d151720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d151720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d146836 q = 1) : d151721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d151721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d146836 q = 1) : d151738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29444 q ha hb
    | true =>
      simp only [d12764, d151738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29423 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d146836 q = 1) : d151739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d151739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d146836 q = 1) : d151744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29445 q ha hb
    | true =>
      simp only [d12797, d151744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d146836 q = 1) : d151745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d151745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d146836 q = 1) : d151746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d151746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d146836 q = 1) : d151747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d151747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d146836 q = 1) : d151748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d151748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12805 q = 1) (hb : d146836 q = 1) : d151752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d151752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29447 q ha hb
    | true =>
      simp only [d12805, d151752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29448 q ha hb
  have h16 (q : Pattern) (ha : d12806 q = 1) (hb : d146836 q = 1) : d151753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d151753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d151753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12807 q = 1) (hb : d146836 q = 1) : d151754 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d151754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12807, d151754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12808 q = 1) (hb : d146836 q = 1) : d151755 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d151755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d151755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12811 q = 1) (hb : d146836 q = 1) : d151758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d151758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29449 q ha hb
    | true =>
      simp only [d12811, d151758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29450 q ha hb
  have h20 (q : Pattern) (ha : d12812 q = 1) (hb : d146836 q = 1) : d151759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d151759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d151759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12813 q = 1) (hb : d146836 q = 1) : d151760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d151760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12813, d151760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12815 q = 1) (hb : d146836 q = 1) : d151762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29451 q ha hb
    | true =>
      simp only [d12815, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29426 q ha hb
  have h23 (q : Pattern) (ha : d115360 q = 1) (hb : d146836 q = 1) : d151763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115360, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12821 q = 1) (hb : d146836 q = 1) : d151765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29452 q ha hb
    | true =>
      simp only [d12821, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12822 q = 1) (hb : d146836 q = 1) : d151766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12822, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115361 q = 1) (hb : d146836 q = 1) : d151767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115361, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115362 q = 1) (hb : d146836 q = 1) : d151768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d151768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115362, d151768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115363 q = 1) (hb : d146836 q = 1) : d151769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d151769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115363, d151769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115364 q = 1) (hb : d146836 q = 1) : d151770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d151770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115364, d151770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro29454 (p : Pattern) (ha : d115371 p = 1) (hb : d146836 p = 1) : d151790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d146836 q = 1) : d151762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29451 q ha hb
    | true =>
      simp only [d12815, d151762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29426 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d146836 q = 1) : d151763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d151763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d146836 q = 1) : d151765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29452 q ha hb
    | true =>
      simp only [d12821, d151765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d146836 q = 1) : d151766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d151766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d146836 q = 1) : d151767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d151767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d146836 q = 1) : d151788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d151788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d151788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d146836 q = 1) : d151789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d151789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d151789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d146836 q = 1) : d151790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d151790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d151790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29455 (p : Pattern) (ha : d12854 p = 1) (hb : d146836 p = 1) : d149051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d116750 q = 1) : d21612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d21612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d21612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d116750 q = 1) : d21482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
    | true =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d116750 q = 1) : d21613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d21613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d21613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d116750 q = 1) : d21483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d116750 q = 1) : d21614 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d21614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d21614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d116750 q = 1) : d21615 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d21615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d21615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h8 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d969 q = 1) (hb : d116750 q = 1) : d21616 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d21616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d969, d21616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12854 q = 1) (hb : d146836 q = 1) : d149051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12854, d146836, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12854, d146836, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29456 (p : Pattern) (ha : d12863 p = 1) (hb : d146836 p = 1) : d151801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d116750 q = 1) : d21314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d116750 q = 1) : d21315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12860 q = 1) (hb : d116750 q = 1) : d21316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12862 q = 1) (hb : d116750 q = 1) : d21623 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d21623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12862, d21623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12863 q = 1) (hb : d146836 q = 1) : d151801 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12863, d146836, d151801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12863, d146836, d151801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro29457 (p : Pattern) (ha : d12873 p = 1) (hb : d146836 p = 1) : d151811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d146836 q = 1) : d151798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d151798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29455 q ha hb
    | true =>
      simp only [d12855, d151798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29410 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d146836 q = 1) : d151799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d151799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d151799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d146836 q = 1) : d151800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d151800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d151800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12864 q = 1) (hb : d146836 q = 1) : d151802 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d151802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29410 q ha hb
    | true =>
      simp only [d12864, d151802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29456 q ha hb
  have h5 (q : Pattern) (ha : d12865 q = 1) (hb : d146836 q = 1) : d151803 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d151803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12865, d151803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12866 q = 1) (hb : d146836 q = 1) : d151804 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d151804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12866, d151804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12867 q = 1) (hb : d146836 q = 1) : d151805 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d151805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12867, d151805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12868 q = 1) (hb : d146836 q = 1) : d151600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29410 q ha hb
    | true =>
      simp only [d12868, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29432 q ha hb
  have h9 (q : Pattern) (ha : d12869 q = 1) (hb : d146836 q = 1) : d151601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12870 q = 1) (hb : d146836 q = 1) : d151602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d146836 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6211 q = 1) (hb : d146836 q = 1) : d151806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29432 q ha hb
    | true =>
      simp only [d6211, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6212 q = 1) (hb : d146836 q = 1) : d151807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6213 q = 1) (hb : d146836 q = 1) : d151808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12871 q = 1) (hb : d146836 q = 1) : d151809 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12871, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12872 q = 1) (hb : d146836 q = 1) : d151810 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d151810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12872, d151810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12873 q = 1) (hb : d146836 q = 1) : d151811 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d151811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12873, d151811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro29458 (p : Pattern) (ha : d12877 p = 1) (hb : d146836 p = 1) : d151816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12868 q = 1) (hb : d146836 q = 1) : d151600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29410 q ha hb
    | true =>
      simp only [d12868, d151600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29432 q ha hb
  have h2 (q : Pattern) (ha : d12869 q = 1) (hb : d146836 q = 1) : d151601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d151601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d146836 q = 1) : d151602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d151602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d146836 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6211 q = 1) (hb : d146836 q = 1) : d151806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29432 q ha hb
    | true =>
      simp only [d6211, d151806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6212 q = 1) (hb : d146836 q = 1) : d151807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d151807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6213 q = 1) (hb : d146836 q = 1) : d151808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d151808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12871 q = 1) (hb : d146836 q = 1) : d151809 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12871, d151809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6214 q = 1) (hb : d146836 q = 1) : d151814 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6214, d151814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12876 q = 1) (hb : d146836 q = 1) : d151815 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d151815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12876, d151815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12877 q = 1) (hb : d146836 q = 1) : d151816 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d151816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12877, d151816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro29459 (p : Pattern) (ha : d12883 p = 1) (hb : d146836 p = 1) : d151822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d146836 q = 1) : d151812 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d151812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29457 q ha hb
    | true =>
      simp only [d12874, d151812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d146836 q = 1) : d151813 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d151813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d151813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d146836 q = 1) : d151817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29458 q ha hb
    | true =>
      simp only [d12878, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d146836 q = 1) : d151818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d146836 q = 1) : d151819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d151819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d151819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d146836 q = 1) : d151820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d151820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d151820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d146836 q = 1) : d151821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d151821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d151821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d146836 q = 1) : d151822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d151822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d151822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29460 (p : Pattern) (ha : d12891 p = 1) (hb : d146836 p = 1) : d151830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d146836 q = 1) : d151817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29458 q ha hb
    | true =>
      simp only [d12878, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d146836 q = 1) : d151818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d146836 q = 1) : d151825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29433 q ha hb
    | true =>
      simp only [d12886, d151825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d146836 q = 1) : d151826 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d151826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12888 q = 1) (hb : d146836 q = 1) : d151827 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d151827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d151827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12889 q = 1) (hb : d146836 q = 1) : d151828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d151828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12889, d151828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12890 q = 1) (hb : d146836 q = 1) : d151829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d151829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12890, d151829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12891 q = 1) (hb : d146836 q = 1) : d151830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d151830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12891, d151830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29461 (p : Pattern) (ha : d12924 p = 1) (hb : d146836 p = 1) : d151836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d146836 q = 1) : d151817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29458 q ha hb
    | true =>
      simp only [d12878, d151817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d146836 q = 1) : d151818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d151818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d146836 q = 1) : d151833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d151833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d151833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d146836 q = 1) : d151834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d151834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d151834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d146836 q = 1) : d151835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d151835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d151835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d146836 q = 1) : d151836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d151836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d151836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29462 (p : Pattern) (ha : d115381 p = 1) (hb : d146836 p = 1) : d151842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d146836 q = 1) : d151831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d151831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29459 q ha hb
    | true =>
      simp only [d12892, d151831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29460 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d146836 q = 1) : d151832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d151832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d151832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d146836 q = 1) : d151837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d151837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29461 q ha hb
    | true =>
      simp only [d12925, d151837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d146836 q = 1) : d151838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d151838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d151838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d146836 q = 1) : d151839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d151839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d151839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d146836 q = 1) : d151840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d151840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d151840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d146836 q = 1) : d151841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d151841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d151841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d146836 q = 1) : d151842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d151842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d151842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29463 (p : Pattern) (ha : d115387 p = 1) (hb : d146836 p = 1) : d151859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d146836 q = 1) : d151692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d151692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d151692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29425 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d146836 q = 1) : d151693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d151693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d151693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d146836 q = 1) : d151702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29425 q ha hb
    | true =>
      simp only [d12724, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29428 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d146836 q = 1) : d151703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d146836 q = 1) : d151704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d151704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d151704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d146836 q = 1) : d151771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d151771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29446 q ha hb
    | true =>
      simp only [d115365, d151771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29453 q ha hb
  have h7 (q : Pattern) (ha : d12840 q = 1) (hb : d146836 q = 1) : d151784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d151784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29429 q ha hb
    | true =>
      simp only [d12840, d151784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29430 q ha hb
  have h8 (q : Pattern) (ha : d115366 q = 1) (hb : d146836 q = 1) : d151785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d151785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d151785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115367 q = 1) (hb : d146836 q = 1) : d151786 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d151786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115367, d151786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115368 q = 1) (hb : d146836 q = 1) : d151787 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d151787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d151787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115372 q = 1) (hb : d146836 q = 1) : d151791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d151791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d151791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29454 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d146836 q = 1) : d151793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d151793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d151793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29431 q ha hb
  have h13 (q : Pattern) (ha : d115373 q = 1) (hb : d146836 q = 1) : d151794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d151794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115373, d151794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115374 q = 1) (hb : d146836 q = 1) : d151795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d151795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115374, d151795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115375 q = 1) (hb : d146836 q = 1) : d151796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d151796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115375, d151796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115376 q = 1) (hb : d146836 q = 1) : d151797 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d151797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115376, d151797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115382 q = 1) (hb : d146836 q = 1) : d151843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d151843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d151843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29462 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d146836 q = 1) : d151854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d151854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d151854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29435 q ha hb
  have h19 (q : Pattern) (ha : d115383 q = 1) (hb : d146836 q = 1) : d151855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d151855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115383, d151855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115384 q = 1) (hb : d146836 q = 1) : d151856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d151856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115384, d151856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115385 q = 1) (hb : d146836 q = 1) : d151857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d151857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115385, d151857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115386 q = 1) (hb : d146836 q = 1) : d151858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d151858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115386, d151858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115387 q = 1) (hb : d146836 q = 1) : d151859 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d151859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115387, d151859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro29464 (p : Pattern) (ha : d115393 p = 1) (hb : d146836 p = 1) : d151865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d146836 q = 1) : d151860 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d151860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d151860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29463 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d146836 q = 1) : d151861 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d151861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d151861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d146836 q = 1) : d151862 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d151862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d151862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d146836 q = 1) : d151863 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d151863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d151863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d146836 q = 1) : d151864 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d151864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d151864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d146836 q = 1) : d151865 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d151865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d151865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29465 (p : Pattern) (ha : d5009 p = 1) (hb : d146836 p = 1) : d149118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d116750 q = 1) : d21759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5009 q = 1) (hb : d146836 q = 1) : d149118 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5009, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29466 (p : Pattern) (ha : d5017 p = 1) (hb : d116750 p = 1) : d21765 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5016 q = 1) : d5016 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5017 q = 1) (hb : d116750 q = 1) : d21765 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5017, d116750, d21765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5017, d116750, d21765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29467 (p : Pattern) (ha : d5023 p = 1) (hb : d146836 p = 1) : d151871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d116750 q = 1) : d21766 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29466 q ha hb
    | true =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d116750 q = 1) : d21767 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d116750 q = 1) : d21768 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d21768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d21768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d116750 q = 1) : d21769 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d21769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d21769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d116750 q = 1) : d21770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d21770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d21770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5023 q = 1) (hb : d146836 q = 1) : d151871 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5023, d146836, d151871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5023, d146836, d151871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29468 (p : Pattern) (ha : d12956 p = 1) (hb : d146836 p = 1) : d149114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1114 q = 1) (hb : d116750 q = 1) : d21746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1114, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12956 q = 1) (hb : d146836 q = 1) : d149114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, d146836, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12956, d146836, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29469 (p : Pattern) (ha : d12961 p = 1) (hb : d146836 p = 1) : d21948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d116750 q = 1) : d21776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12961 q = 1) (hb : d146836 q = 1) : d21948 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d146836, d21948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, d146836, d21948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro29470 (p : Pattern) (ha : d12967 p = 1) (hb : d146836 p = 1) : d151881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29468 q ha hb
    | true =>
      simp only [d12957, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
    | true =>
      simp only [d5024, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29467 q ha hb
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12962 q = 1) (hb : d146836 q = 1) : d151876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
    | true =>
      simp only [d12962, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29469 q ha hb
  have h9 (q : Pattern) (ha : d12963 q = 1) (hb : d146836 q = 1) : d151877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12964 q = 1) (hb : d146836 q = 1) : d151878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12965 q = 1) (hb : d146836 q = 1) : d151879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12965, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12966 q = 1) (hb : d146836 q = 1) : d151880 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12966, d151880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12967 q = 1) (hb : d146836 q = 1) : d151881 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12967, d151881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro29471 (p : Pattern) (ha : d12971 p = 1) (hb : d146836 p = 1) : d151885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12962 q = 1) (hb : d146836 q = 1) : d151876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
    | true =>
      simp only [d12962, d151876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29469 q ha hb
  have h2 (q : Pattern) (ha : d12963 q = 1) (hb : d146836 q = 1) : d151877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d151877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12964 q = 1) (hb : d146836 q = 1) : d151878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d151878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12965 q = 1) (hb : d146836 q = 1) : d151879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12965, d151879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12970 q = 1) (hb : d146836 q = 1) : d151884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d151884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12970, d151884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12971 q = 1) (hb : d146836 q = 1) : d151885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d151885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12971, d151885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29472 (p : Pattern) (ha : d12977 p = 1) (hb : d146836 p = 1) : d151891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d146836 q = 1) : d151890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d146836 q = 1) : d151891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d151891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d151891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29473 (p : Pattern) (ha : d12981 p = 1) (hb : d146836 p = 1) : d151895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d146836 q = 1) : d151894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d146836 q = 1) : d151895 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d151895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d151895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29474 (p : Pattern) (ha : d12987 p = 1) (hb : d146836 p = 1) : d151901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d146836 q = 1) : d151896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29472 q ha hb
    | true =>
      simp only [d12982, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29473 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d146836 q = 1) : d151897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d146836 q = 1) : d151898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d146836 q = 1) : d151899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d146836 q = 1) : d151900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d146836 q = 1) : d151901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29475 (p : Pattern) (ha : d12990 p = 1) (hb : d146836 p = 1) : d151904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d146836 q = 1) : d151890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d151890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d146836 q = 1) : d151904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d151904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d151904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro29476 (p : Pattern) (ha : d12991 p = 1) (hb : d146836 p = 1) : d151905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d146836 q = 1) : d151894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d151894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d146836 q = 1) : d151905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d151905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d151905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29477 (p : Pattern) (ha : d12997 p = 1) (hb : d146836 p = 1) : d151911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d146836 q = 1) : d151896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29472 q ha hb
    | true =>
      simp only [d12982, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29473 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d146836 q = 1) : d151897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d146836 q = 1) : d151898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d146836 q = 1) : d151899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d146836 q = 1) : d151900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d146836 q = 1) : d151906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29475 q ha hb
    | true =>
      simp only [d12992, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29476 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d146836 q = 1) : d151907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d146836 q = 1) : d151908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d146836 q = 1) : d151909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d146836 q = 1) : d151910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d146836 q = 1) : d151911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29478 (p : Pattern) (ha : d13040 p = 1) (hb : d146836 p = 1) : d151946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29468 q ha hb
    | true =>
      simp only [d12957, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
    | true =>
      simp only [d5024, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29467 q ha hb
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5027 q = 1) (hb : d146836 q = 1) : d151944 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d151944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5027, d151944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13039 q = 1) (hb : d146836 q = 1) : d151945 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d151945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13039, d151945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13040 q = 1) (hb : d146836 q = 1) : d151946 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d151946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13040, d151946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro29479 (p : Pattern) (ha : d13050 p = 1) (hb : d146836 p = 1) : d151956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29478 q ha hb
    | true =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d146836 q = 1) : d151953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d151953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d146836 q = 1) : d151954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d151954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d146836 q = 1) : d151955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d151955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d146836 q = 1) : d151956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d151956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d151956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29480 (p : Pattern) (ha : d13134 p = 1) (hb : d146836 p = 1) : d152002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d146836 q = 1) : d151992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d151992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29479 q ha hb
    | true =>
      simp only [d13124, d151992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29473 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d146836 q = 1) : d151993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d151993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d151993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d146836 q = 1) : d151994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d151994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d151994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d146836 q = 1) : d151995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d151995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d151995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d146836 q = 1) : d151996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d151996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d151996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d146836 q = 1) : d151997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29473 q ha hb
    | true =>
      simp only [d13129, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d146836 q = 1) : d151998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d146836 q = 1) : d151999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d146836 q = 1) : d152000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d146836 q = 1) : d152001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d146836 q = 1) : d152002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d152002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d152002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29481 (p : Pattern) (ha : d13140 p = 1) (hb : d146836 p = 1) : d152008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d146836 q = 1) : d151997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29473 q ha hb
    | true =>
      simp only [d13129, d151997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d146836 q = 1) : d151998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d151998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d146836 q = 1) : d151999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d151999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d146836 q = 1) : d152000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d152000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d146836 q = 1) : d152001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d152001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d146836 q = 1) : d152003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29476 q ha hb
    | true =>
      simp only [d13135, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d146836 q = 1) : d152004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d146836 q = 1) : d152005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d146836 q = 1) : d152006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d146836 q = 1) : d152007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d146836 q = 1) : d152008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d152008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d152008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29482 (p : Pattern) (ha : d13149 p = 1) (hb : d146836 p = 1) : d152017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d146836 q = 1) : d152003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29476 q ha hb
    | true =>
      simp only [d13135, d152003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d146836 q = 1) : d152004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d152004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d146836 q = 1) : d152005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d152005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d146836 q = 1) : d152006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d152006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d146836 q = 1) : d152007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d152007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d146836 q = 1) : d152017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d152017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d152017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29483 (p : Pattern) (ha : d6349 p = 1) (hb : d146836 p = 1) : d149258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d116750 q = 1) : d22068 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6349 q = 1) (hb : d146836 q = 1) : d149258 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6349, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29484 (p : Pattern) (ha : d13190 p = 1) (hb : d146836 p = 1) : d22174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d116750 q = 1) : d22096 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d146836 q = 1) : d22174 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d146836, d22174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d146836, d22174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro29485 (p : Pattern) (ha : d13196 p = 1) (hb : d146836 p = 1) : d152057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13191 q = 1) (hb : d146836 q = 1) : d152052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29483 q ha hb
    | true =>
      simp only [d13191, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29484 q ha hb
  have h2 (q : Pattern) (ha : d13192 q = 1) (hb : d146836 q = 1) : d152053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13193 q = 1) (hb : d146836 q = 1) : d152054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13194 q = 1) (hb : d146836 q = 1) : d152055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13194, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13195 q = 1) (hb : d146836 q = 1) : d152056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d152056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13195, d152056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13196 q = 1) (hb : d146836 q = 1) : d152057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d152057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13196, d152057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29486 (p : Pattern) (ha : d13260 p = 1) (hb : d146836 p = 1) : d152084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d146836 q = 1) : d152058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29485 q ha hb
    | true =>
      simp only [d13197, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d146836 q = 1) : d152059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d146836 q = 1) : d152081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d152081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d152081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d146836 q = 1) : d152082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d152082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d152082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d146836 q = 1) : d152083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d152083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d152083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d146836 q = 1) : d152084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d152084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d152084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro29487 (p : Pattern) (ha : d13266 p = 1) (hb : d146836 p = 1) : d152090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d146836 q = 1) : d152085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d152085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29486 q ha hb
    | true =>
      simp only [d13261, d152085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d146836 q = 1) : d152086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d152086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d152086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d146836 q = 1) : d152087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d152087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d152087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d146836 q = 1) : d152088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d152088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d152088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d146836 q = 1) : d152089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d152089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d152089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d146836 q = 1) : d152090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d152090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d152090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29488 (p : Pattern) (ha : d13002 p = 1) (hb : d146836 p = 1) : d151916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d146836 q = 1) : d151915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d146836 q = 1) : d151916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d151916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d151916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29489 (p : Pattern) (ha : d13004 p = 1) (hb : d146836 p = 1) : d151918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d146836 q = 1) : d151893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d151893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d146836 q = 1) : d151917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d151917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d146836 q = 1) : d151918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d151918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d151918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29490 (p : Pattern) (ha : d13011 p = 1) (hb : d146836 p = 1) : d151925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d146836 q = 1) : d151923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d151923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d146836 q = 1) : d151924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d151924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d146836 q = 1) : d151925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d151925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d151925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29491 (p : Pattern) (ha : d13014 p = 1) (hb : d146836 p = 1) : d151928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d146836 q = 1) : d151892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d151892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d146836 q = 1) : d151926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d151926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d146836 q = 1) : d151927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d151927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d146836 q = 1) : d151928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d151928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d151928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29492 (p : Pattern) (ha : d13018 p = 1) (hb : d146836 p = 1) : d149176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d116750 q = 1) : d21835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
    | true =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d116750 q = 1) : d21836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d116750 q = 1) : d21837 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d21837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d21837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d116750 q = 1) : d21838 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d21838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d21838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1214 q = 1) (hb : d116750 q = 1) : d21839 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d21839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1214, d21839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13018 q = 1) (hb : d146836 q = 1) : d149176 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, d146836, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13018, d146836, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro29493 (p : Pattern) (ha : d9813 p = 1) (hb : d116750 p = 1) : d21850 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d9812 q = 1) : d9812 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9813 q = 1) (hb : d116750 q = 1) : d21850 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9813, d116750, d21850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9813, d116750, d21850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro29494 (p : Pattern) (ha : d13030 p = 1) (hb : d146836 p = 1) : d151935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d116750 q = 1) : d21851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29493 q ha hb
    | true =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9816 q = 1) (hb : d116750 q = 1) : d21852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13022 q = 1) (hb : d116750 q = 1) : d21853 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d21853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d21853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d116750 q = 1) : d21854 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d21854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13023, d21854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13028 q = 1) (hb : d116750 q = 1) : d13028 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13029 q = 1) (hb : d116750 q = 1) : d21855 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, d21855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13029, d21855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13030 q = 1) (hb : d146836 q = 1) : d151935 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13030, d146836, d151935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13030, d146836, d151935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29495 (p : Pattern) (ha : d13036 p = 1) (hb : d146836 p = 1) : d151941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d146836 q = 1) : d151932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d151932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29492 q ha hb
    | true =>
      simp only [d13019, d151932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29468 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d146836 q = 1) : d151933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d151933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d151933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d146836 q = 1) : d151934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d151934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d151934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13031 q = 1) (hb : d146836 q = 1) : d151936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d151936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29468 q ha hb
    | true =>
      simp only [d13031, d151936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29494 q ha hb
  have h5 (q : Pattern) (ha : d13032 q = 1) (hb : d146836 q = 1) : d151937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d151937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13032, d151937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13033 q = 1) (hb : d146836 q = 1) : d151938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d151938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13033, d151938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13034 q = 1) (hb : d146836 q = 1) : d151939 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d151939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13034, d151939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12957 q = 1) (hb : d146836 q = 1) : d151868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29468 q ha hb
    | true =>
      simp only [d12957, d151868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
  have h9 (q : Pattern) (ha : d12958 q = 1) (hb : d146836 q = 1) : d151869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d151869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12959 q = 1) (hb : d146836 q = 1) : d151870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d151870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5024 q = 1) (hb : d146836 q = 1) : d151872 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29465 q ha hb
    | true =>
      simp only [d5024, d151872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29467 q ha hb
  have h12 (q : Pattern) (ha : d5025 q = 1) (hb : d146836 q = 1) : d151873 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d151873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5026 q = 1) (hb : d146836 q = 1) : d151874 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d151874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12960 q = 1) (hb : d146836 q = 1) : d151875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12960, d151875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13035 q = 1) (hb : d146836 q = 1) : d151940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d151940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13035, d151940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13036 q = 1) (hb : d146836 q = 1) : d151941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d151941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13036, d151941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro29496 (p : Pattern) (ha : d13046 p = 1) (hb : d146836 p = 1) : d151952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d146836 q = 1) : d151942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29495 q ha hb
    | true =>
      simp only [d13037, d151942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d146836 q = 1) : d151943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d151943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d146836 q = 1) : d151947 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29478 q ha hb
    | true =>
      simp only [d13041, d151947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d146836 q = 1) : d151948 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d151948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d146836 q = 1) : d151949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d151949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d146836 q = 1) : d151950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d151950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d146836 q = 1) : d151951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d151951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d146836 q = 1) : d151952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d151952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d151952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro29497 (p : Pattern) (ha : d13091 p = 1) (hb : d146836 p = 1) : d151962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d146836 q = 1) : d151959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d151959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d146836 q = 1) : d151960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d151960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d146836 q = 1) : d151961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d151961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d146836 q = 1) : d151962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d151962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d151962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro29498 (p : Pattern) (ha : d115400 p = 1) (hb : d146836 p = 1) : d151968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d146836 q = 1) : d151919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29488 q ha hb
    | true =>
      simp only [d13005, d151919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29489 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d146836 q = 1) : d151920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d151920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d146836 q = 1) : d151921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d151921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d146836 q = 1) : d151922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d151922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d146836 q = 1) : d151929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29490 q ha hb
    | true =>
      simp only [d13015, d151929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29491 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d146836 q = 1) : d151930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d151930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d146836 q = 1) : d151931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d151931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d146836 q = 1) : d151957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29496 q ha hb
    | true =>
      simp only [d13051, d151957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29479 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d146836 q = 1) : d151958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d151958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d146836 q = 1) : d151963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29497 q ha hb
    | true =>
      simp only [d13092, d151963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d146836 q = 1) : d151964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d151964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d146836 q = 1) : d151965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d151965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d146836 q = 1) : d151966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d151966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d146836 q = 1) : d151967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d151967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115400 q = 1) (hb : d146836 q = 1) : d151968 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d151968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d151968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro29499 (p : Pattern) (ha : d13098 p = 1) (hb : d146836 p = 1) : d151969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d146836 q = 1) : d151882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29470 q ha hb
    | true =>
      simp only [d12968, d151882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d146836 q = 1) : d151883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d151883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d146836 q = 1) : d151886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29471 q ha hb
    | true =>
      simp only [d12972, d151886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d146836 q = 1) : d151887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d151887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d146836 q = 1) : d151888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d151888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d146836 q = 1) : d151889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d151889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d146836 q = 1) : d151915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d151915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d146836 q = 1) : d151969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d151969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d151969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
