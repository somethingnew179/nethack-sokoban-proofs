import NetHack.Soko22Hazard87.AndIntroBlocks0101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro25500 (p : Pattern) (ha : d88291 p = 1) (hb : d140102 p = 1) : d140784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78842 q = 1) (hb : d88190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d78842, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78842, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25482 q ha hb
  have h2 (q : Pattern) (ha : d78843 q = 1) (hb : d88191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d78843, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78843, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78844 q = 1) (hb : d88192 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d78844, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78844, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d78845 q = 1) (hb : d88193 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d78845, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78845, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78846 q = 1) (hb : d88194 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d78846, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78846, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88286 q = 1) (hb : d140097 q = 1) : d140779 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d88286, d140097, d140779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88286, d140097, d140779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25499 q ha hb
  have h7 (q : Pattern) (ha : d88287 q = 1) (hb : d140098 q = 1) : d140780 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d88287, d140098, d140780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88287, d140098, d140780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88288 q = 1) (hb : d140099 q = 1) : d140781 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d88288, d140099, d140781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88288, d140099, d140781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88289 q = 1) (hb : d140100 q = 1) : d140782 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d88289, d140100, d140782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88289, d140100, d140782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88290 q = 1) (hb : d140101 q = 1) : d140783 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d88290, d140101, d140783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88290, d140101, d140783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88291 q = 1) (hb : d140102 q = 1) : d140784 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d88291, d140102, d140784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d88291, d140102, d140784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25501 (p : Pattern) (ha : d78940 p = 1) (hb : d88293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10863 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52222 q = 1) (hb : d88292 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d78940 q = 1) (hb : d88293 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d78940, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78940, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25502 (p : Pattern) (ha : d78945 p = 1) (hb : d88299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78941 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25501 q ha hb
    | true =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78942 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78944 q = 1) (hb : d88298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78944, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78944, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78945 q = 1) (hb : d88299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78945, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78945, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25503 (p : Pattern) (ha : d78951 p = 1) (hb : d88305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78946 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
    | true =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78947 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78947, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78947, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78948 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78948, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78948, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78949 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78949, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78949, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78950 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78950, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78950, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78951 q = 1) (hb : d88305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78951, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78951, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25504 (p : Pattern) (ha : d78954 p = 1) (hb : d88308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78941 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25501 q ha hb
    | true =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78942 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78944 q = 1) (hb : d88298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78944, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78944, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78954 q = 1) (hb : d88308 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78954, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78954, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25505 (p : Pattern) (ha : d78960 p = 1) (hb : d88314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78946 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
    | true =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78947 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78947, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78947, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78948 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78948, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78948, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78949 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78949, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78949, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78950 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78950, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78950, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78955 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25504 q ha hb
    | true =>
      simp only [d78955, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78956 q = 1) (hb : d88310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78956, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78956, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78957 q = 1) (hb : d88311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78957, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78957, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78958 q = 1) (hb : d88312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78958, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78958, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78959 q = 1) (hb : d88313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78959, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78959, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78960 q = 1) (hb : d88314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78960, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78960, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25506 (p : Pattern) (ha : d78965 p = 1) (hb : d88319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78941 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25501 q ha hb
    | true =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78942 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78964 q = 1) (hb : d88318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78964, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78964, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78965 q = 1) (hb : d88319 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78965, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78965, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25507 (p : Pattern) (ha : d78972 p = 1) (hb : d88326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78941 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25501 q ha hb
    | true =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78942 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78970 q = 1) (hb : d88324 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78970, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78970, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78971 q = 1) (hb : d88325 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78971, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78971, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78972 q = 1) (hb : d88326 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78972, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78972, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25508 (p : Pattern) (ha : d78976 p = 1) (hb : d88331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10745 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10745, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52127 q = 1) (hb : d88330 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d78976 q = 1) (hb : d88331 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d78976, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78976, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25509 (p : Pattern) (ha : d78981 p = 1) (hb : d88337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78977 q = 1) (hb : d88332 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78977, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25508 q ha hb
    | true =>
      simp only [d78977, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78978 q = 1) (hb : d88333 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78978, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78978, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78978 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78978 q = 1) (hb : d88334 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78979 q = 1) (hb : d88335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78979, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78979, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78980 q = 1) (hb : d88336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78980, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78980, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78981 q = 1) (hb : d88337 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78981, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78981, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25510 (p : Pattern) (ha : d140108 p = 1) (hb : d140386 p = 1) : d140788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78966 q = 1) (hb : d88320 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78966, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25506 q ha hb
    | true =>
      simp only [d78966, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78967 q = 1) (hb : d88321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78967, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78967, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78968 q = 1) (hb : d88322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78968, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78968, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78969 q = 1) (hb : d88323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78969, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78969, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78973 q = 1) (hb : d88327 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78973, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25507 q ha hb
    | true =>
      simp only [d78973, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78974 q = 1) (hb : d88328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78974, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78974, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78975 q = 1) (hb : d88329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78975, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78975, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140103 q = 1) (hb : d140381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140103, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25509 q ha hb
    | true =>
      simp only [d140103, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78946 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140104 q = 1) (hb : d140382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140104, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140104, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d88352 q = 1) : d88352 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140105 q = 1) (hb : d140383 q = 1) : d140785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140105, d140383, d140785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140105, d140383, d140785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140106 q = 1) (hb : d140384 q = 1) : d140786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140106, d140384, d140786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140106, d140384, d140786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140107 q = 1) (hb : d140385 q = 1) : d140787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140107, d140385, d140787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140107, d140385, d140787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d140108 q = 1) (hb : d140386 q = 1) : d140788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140108, d140386, d140788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140108, d140386, d140788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25511 (p : Pattern) (ha : d78995 p = 1) (hb : d88357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78941 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25501 q ha hb
    | true =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78942 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78943 q = 1) (hb : d88297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78943, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78964 q = 1) (hb : d88318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78964, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78964, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78995 q = 1) (hb : d88357 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78995, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78995, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25512 (p : Pattern) (ha : d79000 p = 1) (hb : d88362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78941 q = 1) (hb : d88294 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25501 q ha hb
    | true =>
      simp only [d78941, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78942 q = 1) (hb : d88295 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78942, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78942 q = 1) (hb : d88296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78970 q = 1) (hb : d88324 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78970, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78970, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78971 q = 1) (hb : d88325 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78971, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78971, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79000 q = 1) (hb : d88362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79000, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79000, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25513 (p : Pattern) (ha : d79004 p = 1) (hb : d88366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78977 q = 1) (hb : d88332 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78977, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25508 q ha hb
    | true =>
      simp only [d78977, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78978 q = 1) (hb : d88333 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78978, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78978, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78978 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78978 q = 1) (hb : d88334 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78979 q = 1) (hb : d88335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78979, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78979, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78980 q = 1) (hb : d88336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78980, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78980, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79004 q = 1) (hb : d88366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79004, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79004, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25514 (p : Pattern) (ha : d140114 p = 1) (hb : d140392 p = 1) : d140792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78966 q = 1) (hb : d88320 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78966, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25506 q ha hb
    | true =>
      simp only [d78966, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78967 q = 1) (hb : d88321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78967, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78967, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78968 q = 1) (hb : d88322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78968, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78968, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78969 q = 1) (hb : d88323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78969, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78969, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78973 q = 1) (hb : d88327 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78973, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25507 q ha hb
    | true =>
      simp only [d78973, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78974 q = 1) (hb : d88328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78974, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78974, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78975 q = 1) (hb : d88329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78975, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78975, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140103 q = 1) (hb : d140381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140103, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25509 q ha hb
    | true =>
      simp only [d140103, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78946 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140104 q = 1) (hb : d140382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140104, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140104, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d88352 q = 1) : d88352 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140105 q = 1) (hb : d140383 q = 1) : d140785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140105, d140383, d140785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140105, d140383, d140785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140106 q = 1) (hb : d140384 q = 1) : d140786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140106, d140384, d140786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140106, d140384, d140786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140107 q = 1) (hb : d140385 q = 1) : d140787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140107, d140385, d140787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140107, d140385, d140787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d78996 q = 1) (hb : d88358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78996, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25511 q ha hb
    | true =>
      simp only [d78996, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d78997 q = 1) (hb : d88359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78997, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78997, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d78998 q = 1) (hb : d88360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78998, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d78998, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d78999 q = 1) (hb : d88361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78999, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78999, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79001 q = 1) (hb : d88363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79001, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25512 q ha hb
    | true =>
      simp only [d79001, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79002 q = 1) (hb : d88364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79002, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79002, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79003 q = 1) (hb : d88365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79003, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79003, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d140109 q = 1) (hb : d140387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140109, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25513 q ha hb
    | true =>
      simp only [d140109, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25504 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d78955 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d140110 q = 1) (hb : d140388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140110, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d140110, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d88370 q = 1) : d88370 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d140111 q = 1) (hb : d140389 q = 1) : d140789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140111, d140389, d140789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d140111, d140389, d140789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d140112 q = 1) (hb : d140390 q = 1) : d140790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140112, d140390, d140790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d140112, d140390, d140790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d140113 q = 1) (hb : d140391 q = 1) : d140791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140113, d140391, d140791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140113, d140391, d140791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d140114 q = 1) (hb : d140392 q = 1) : d140792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140114, d140392, d140792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d140114, d140392, d140792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25515 (p : Pattern) (ha : d140116 p = 1) (hb : d140394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78946 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
    | true =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78947 q = 1) (hb : d88301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78947, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78947, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78948 q = 1) (hb : d88302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78948, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78948, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78949 q = 1) (hb : d88303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78949, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78949, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78950 q = 1) (hb : d88304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78950, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78950, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140116 q = 1) (hb : d140394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140116, d140394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140116, d140394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25516 (p : Pattern) (ha : d140123 p = 1) (hb : d140401 p = 1) : d140797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140109 q = 1) (hb : d140387 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140109, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25513 q ha hb
    | true =>
      simp only [d140109, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25504 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140110 q = 1) (hb : d140388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140110, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140110, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d88370 q = 1) : d88370 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140111 q = 1) (hb : d140389 q = 1) : d140789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140111, d140389, d140789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140111, d140389, d140789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140121 q = 1) (hb : d140399 q = 1) : d140790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140121, d140399, d140790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140121, d140399, d140790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140122 q = 1) (hb : d140400 q = 1) : d140791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140122, d140400, d140791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140122, d140400, d140791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140123 q = 1) (hb : d140401 q = 1) : d140797 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140123, d140401, d140797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140123, d140401, d140797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25517 (p : Pattern) (ha : d79032 p = 1) (hb : d88395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10814 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10815 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10815, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10816 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10816, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10817 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10817, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52187 q = 1) (hb : d88394 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79032 q = 1) (hb : d88395 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79032, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79032, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25518 (p : Pattern) (ha : d79037 p = 1) (hb : d88401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79033 q = 1) (hb : d88396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79033, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25517 q ha hb
    | true =>
      simp only [d79033, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79034 q = 1) (hb : d88397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79034, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79034, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79034 q = 1) (hb : d88398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79035 q = 1) (hb : d88399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79035, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79035, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79036 q = 1) (hb : d88400 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79036, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79036, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79037 q = 1) (hb : d88401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79037, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79037, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25519 (p : Pattern) (ha : d79045 p = 1) (hb : d88417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11021 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52377 q = 1) (hb : d88416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79045 q = 1) (hb : d88417 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79045, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79045, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25520 (p : Pattern) (ha : d79050 p = 1) (hb : d88423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79046 q = 1) (hb : d88418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79046, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25519 q ha hb
    | true =>
      simp only [d79046, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79047 q = 1) (hb : d88419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79047, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79047, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79047 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79047 q = 1) (hb : d88420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79048 q = 1) (hb : d88421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79048, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79048, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79049 q = 1) (hb : d88422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79049, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79049, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79050 q = 1) (hb : d88423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79050, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79050, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25521 (p : Pattern) (ha : d140134 p = 1) (hb : d140412 p = 1) : d140806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140129 q = 1) (hb : d140407 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140129, d140407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25518 q ha hb
    | true =>
      simp only [d140129, d140407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25520 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140130 q = 1) (hb : d140408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140130, d140408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140130, d140408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d88425 q = 1) : d88425 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140131 q = 1) (hb : d140409 q = 1) : d140803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140131, d140409, d140803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140131, d140409, d140803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140132 q = 1) (hb : d140410 q = 1) : d140804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140132, d140410, d140804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140132, d140410, d140804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140133 q = 1) (hb : d140411 q = 1) : d140805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140133, d140411, d140805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140133, d140411, d140805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140134 q = 1) (hb : d140412 q = 1) : d140806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140134, d140412, d140806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140134, d140412, d140806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25522 (p : Pattern) (ha : d140140 p = 1) (hb : d140418 p = 1) : d140812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78952 q = 1) (hb : d88306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78952, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78952, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25503 q ha hb
  have h2 (q : Pattern) (ha : d78953 q = 1) (hb : d88307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78953, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78953, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78961 q = 1) (hb : d88315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78961, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25503 q ha hb
    | true =>
      simp only [d78961, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25505 q ha hb
  have h4 (q : Pattern) (ha : d78962 q = 1) (hb : d88316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78962, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78962, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78963 q = 1) (hb : d88317 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78963, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78963, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140115 q = 1) (hb : d140393 q = 1) : d140793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140115, d140393, d140793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25510 q ha hb
    | true =>
      simp only [d140115, d140393, d140793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25514 q ha hb
  have h7 (q : Pattern) (ha : d140117 q = 1) (hb : d140395 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140117, d140395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25515 q ha hb
    | true =>
      simp only [d140117, d140395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140118 q = 1) (hb : d140396 q = 1) : d140794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140118, d140396, d140794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140118, d140396, d140794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d140119 q = 1) (hb : d140397 q = 1) : d140795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140119, d140397, d140795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140119, d140397, d140795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d140120 q = 1) (hb : d140398 q = 1) : d140796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140120, d140398, d140796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140120, d140398, d140796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140124 q = 1) (hb : d140402 q = 1) : d140798 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140124, d140402, d140798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140124, d140402, d140798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25516 q ha hb
  have h12 (q : Pattern) (ha : d140125 q = 1) (hb : d140403 q = 1) : d140799 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140125, d140403, d140799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d140125, d140403, d140799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d140126 q = 1) (hb : d140404 q = 1) : d140800 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140126, d140404, d140800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d140126, d140404, d140800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d140127 q = 1) (hb : d140405 q = 1) : d140801 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140127, d140405, d140801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d140127, d140405, d140801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d140128 q = 1) (hb : d140406 q = 1) : d140802 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140128, d140406, d140802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140128, d140406, d140802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d140135 q = 1) (hb : d140413 q = 1) : d140807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140135, d140413, d140807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140135, d140413, d140807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25521 q ha hb
  have h17 (q : Pattern) (ha : d140136 q = 1) (hb : d140414 q = 1) : d140808 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140136, d140414, d140808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d140136, d140414, d140808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d140137 q = 1) (hb : d140415 q = 1) : d140809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140137, d140415, d140809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d140137, d140415, d140809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d140138 q = 1) (hb : d140416 q = 1) : d140810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140138, d140416, d140810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140138, d140416, d140810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d140139 q = 1) (hb : d140417 q = 1) : d140811 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140139, d140417, d140811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d140139, d140417, d140811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d140140 q = 1) (hb : d140418 q = 1) : d140812 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140140, d140418, d140812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140140, d140418, d140812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25523 (p : Pattern) (ha : d140146 p = 1) (hb : d140424 p = 1) : d140818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140141 q = 1) (hb : d140419 q = 1) : d140813 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140141, d140419, d140813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140141, d140419, d140813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25522 q ha hb
  have h2 (q : Pattern) (ha : d140142 q = 1) (hb : d140420 q = 1) : d140814 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140142, d140420, d140814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140142, d140420, d140814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140143 q = 1) (hb : d140421 q = 1) : d140815 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140143, d140421, d140815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140143, d140421, d140815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140144 q = 1) (hb : d140422 q = 1) : d140816 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140144, d140422, d140816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140144, d140422, d140816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140145 q = 1) (hb : d140423 q = 1) : d140817 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140145, d140423, d140817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140145, d140423, d140817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140146 q = 1) (hb : d140424 q = 1) : d140818 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140146, d140424, d140818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140146, d140424, d140818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25524 (p : Pattern) (ha : d79071 p = 1) (hb : d88444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11103 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11103, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52444 q = 1) (hb : d88443 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79071 q = 1) (hb : d88444 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79071, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79071, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25525 (p : Pattern) (ha : d79076 p = 1) (hb : d88450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79072 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25524 q ha hb
    | true =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79073 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79075 q = 1) (hb : d88449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79075, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79075, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79076 q = 1) (hb : d88450 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79076, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79076, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25526 (p : Pattern) (ha : d79082 p = 1) (hb : d88456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79077 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
    | true =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79078 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79078, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79078, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79079 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79079, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79079, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79080 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79080, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79080, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79081 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79081, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79081, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79082 q = 1) (hb : d88456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79082, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79082, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25527 (p : Pattern) (ha : d79085 p = 1) (hb : d88459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79072 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25524 q ha hb
    | true =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79073 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79075 q = 1) (hb : d88449 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79075, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79075, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79085 q = 1) (hb : d88459 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79085, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79085, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25528 (p : Pattern) (ha : d79091 p = 1) (hb : d88465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79077 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
    | true =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79078 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79078, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79078, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79079 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79079, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79079, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79080 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79080, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79080, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79081 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79081, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79081, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79086 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25527 q ha hb
    | true =>
      simp only [d79086, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79087 q = 1) (hb : d88461 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79087, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79087, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79088 q = 1) (hb : d88462 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79088, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79088, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79089 q = 1) (hb : d88463 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79089, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79089, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79090 q = 1) (hb : d88464 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79090, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79090, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79091 q = 1) (hb : d88465 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79091, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79091, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25529 (p : Pattern) (ha : d79096 p = 1) (hb : d88470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79072 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25524 q ha hb
    | true =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79073 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79095 q = 1) (hb : d88469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79095, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79095, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79096 q = 1) (hb : d88470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79096, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79096, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25530 (p : Pattern) (ha : d79103 p = 1) (hb : d88477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79072 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25524 q ha hb
    | true =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79073 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79101 q = 1) (hb : d88475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79101, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79101, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79102 q = 1) (hb : d88476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79102, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79102, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79103 q = 1) (hb : d88477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79103, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79103, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25531 (p : Pattern) (ha : d79107 p = 1) (hb : d88482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11096 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11097 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11097, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11098 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11098, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11099 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11100 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11100, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11101 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11101, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11102 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11102, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52443 q = 1) (hb : d88481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79107 q = 1) (hb : d88482 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79107, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79107, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25532 (p : Pattern) (ha : d79112 p = 1) (hb : d88488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79108 q = 1) (hb : d88483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79108, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25531 q ha hb
    | true =>
      simp only [d79108, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79109 q = 1) (hb : d88484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79109, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79109, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79109 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79109 q = 1) (hb : d88485 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79110 q = 1) (hb : d88486 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79110, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79110, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79111 q = 1) (hb : d88487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79111, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79111, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79112 q = 1) (hb : d88488 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79112, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79112, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25533 (p : Pattern) (ha : d140153 p = 1) (hb : d140441 p = 1) : d140823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79097 q = 1) (hb : d88471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79097, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25529 q ha hb
    | true =>
      simp only [d79097, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79098 q = 1) (hb : d88472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79098, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79098, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79099 q = 1) (hb : d88473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79099, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79099, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79100 q = 1) (hb : d88474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79100, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79100, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79104 q = 1) (hb : d88478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79104, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25530 q ha hb
    | true =>
      simp only [d79104, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79105 q = 1) (hb : d88479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79105, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79105, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79106 q = 1) (hb : d88480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79106, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79106, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140148 q = 1) (hb : d140426 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140148, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25532 q ha hb
    | true =>
      simp only [d140148, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79077 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140149 q = 1) (hb : d140427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140149, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140149, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140437 q = 1) : d140437 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140150 q = 1) (hb : d140438 q = 1) : d140820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140150, d140438, d140820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140150, d140438, d140820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140151 q = 1) (hb : d140439 q = 1) : d140821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140151, d140439, d140821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140151, d140439, d140821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140152 q = 1) (hb : d140440 q = 1) : d140822 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140152, d140440, d140822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140152, d140440, d140822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d140153 q = 1) (hb : d140441 q = 1) : d140823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140153, d140441, d140823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140153, d140441, d140823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25534 (p : Pattern) (ha : d79126 p = 1) (hb : d88508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79072 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25524 q ha hb
    | true =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79073 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79074 q = 1) (hb : d88448 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79074, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79095 q = 1) (hb : d88469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79095, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79095, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79126 q = 1) (hb : d88508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79126, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79126, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25535 (p : Pattern) (ha : d79131 p = 1) (hb : d88513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79072 q = 1) (hb : d88445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25524 q ha hb
    | true =>
      simp only [d79072, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79073 q = 1) (hb : d88446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79073, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79073 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79073 q = 1) (hb : d88447 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79101 q = 1) (hb : d88475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79101, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79101, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79102 q = 1) (hb : d88476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79102, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79102, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79131 q = 1) (hb : d88513 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79131, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79131, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25536 (p : Pattern) (ha : d79135 p = 1) (hb : d88517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79108 q = 1) (hb : d88483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79108, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25531 q ha hb
    | true =>
      simp only [d79108, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79109 q = 1) (hb : d88484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79109, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79109, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79109 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79109 q = 1) (hb : d88485 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79110 q = 1) (hb : d88486 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79110, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79110, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79111 q = 1) (hb : d88487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79111, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79111, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79135 q = 1) (hb : d88517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79135, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79135, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25537 (p : Pattern) (ha : d140159 p = 1) (hb : d140450 p = 1) : d140827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79097 q = 1) (hb : d88471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79097, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25529 q ha hb
    | true =>
      simp only [d79097, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79098 q = 1) (hb : d88472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79098, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79098, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79099 q = 1) (hb : d88473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79099, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79099, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79100 q = 1) (hb : d88474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79100, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79100, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79104 q = 1) (hb : d88478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79104, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25530 q ha hb
    | true =>
      simp only [d79104, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79105 q = 1) (hb : d88479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79105, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79105, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79106 q = 1) (hb : d88480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79106, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79106, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140148 q = 1) (hb : d140426 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140148, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25532 q ha hb
    | true =>
      simp only [d140148, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79077 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140149 q = 1) (hb : d140427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140149, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140149, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140437 q = 1) : d140437 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140150 q = 1) (hb : d140438 q = 1) : d140820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140150, d140438, d140820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140150, d140438, d140820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140151 q = 1) (hb : d140439 q = 1) : d140821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140151, d140439, d140821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140151, d140439, d140821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140152 q = 1) (hb : d140440 q = 1) : d140822 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140152, d140440, d140822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140152, d140440, d140822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79127 q = 1) (hb : d88509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79127, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25534 q ha hb
    | true =>
      simp only [d79127, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d79128 q = 1) (hb : d88510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79128, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79128, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79129 q = 1) (hb : d88511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79129, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79129, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79130 q = 1) (hb : d88512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79130, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79130, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79132 q = 1) (hb : d88514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79132, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25535 q ha hb
    | true =>
      simp only [d79132, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79133 q = 1) (hb : d88515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79133, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79133, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79134 q = 1) (hb : d88516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79134, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79134, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d140154 q = 1) (hb : d140442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140154, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25536 q ha hb
    | true =>
      simp only [d140154, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25527 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d79086 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d140155 q = 1) (hb : d140443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140155, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d140155, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d140446 q = 1) : d140446 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d140156 q = 1) (hb : d140447 q = 1) : d140824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140156, d140447, d140824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d140156, d140447, d140824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d140157 q = 1) (hb : d140448 q = 1) : d140825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140157, d140448, d140825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d140157, d140448, d140825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d140158 q = 1) (hb : d140449 q = 1) : d140826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140158, d140449, d140826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140158, d140449, d140826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d140159 q = 1) (hb : d140450 q = 1) : d140827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140159, d140450, d140827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d140159, d140450, d140827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25538 (p : Pattern) (ha : d140161 p = 1) (hb : d140452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79077 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
    | true =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79078 q = 1) (hb : d88452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79078, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79078, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79079 q = 1) (hb : d88453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79079, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79079, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79080 q = 1) (hb : d88454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79080, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79080, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79081 q = 1) (hb : d88455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79081, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79081, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140161 q = 1) (hb : d140452 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140161, d140452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140161, d140452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25539 (p : Pattern) (ha : d140168 p = 1) (hb : d140459 p = 1) : d140832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140154 q = 1) (hb : d140442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140154, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25536 q ha hb
    | true =>
      simp only [d140154, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25527 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140155 q = 1) (hb : d140443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140155, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140155, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140446 q = 1) : d140446 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140156 q = 1) (hb : d140447 q = 1) : d140824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140156, d140447, d140824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140156, d140447, d140824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140166 q = 1) (hb : d140457 q = 1) : d140825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140166, d140457, d140825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140166, d140457, d140825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140167 q = 1) (hb : d140458 q = 1) : d140826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140167, d140458, d140826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140167, d140458, d140826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140168 q = 1) (hb : d140459 q = 1) : d140832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140168, d140459, d140832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140168, d140459, d140832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25540 (p : Pattern) (ha : d79163 p = 1) (hb : d88546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11267 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11268 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11268, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11269 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11269, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11274 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11274, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52609 q = 1) (hb : d88545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79163 q = 1) (hb : d88546 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79163, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79163, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25541 (p : Pattern) (ha : d79168 p = 1) (hb : d88552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79164 q = 1) (hb : d88547 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79164, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25540 q ha hb
    | true =>
      simp only [d79164, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79165 q = 1) (hb : d88548 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79165, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79165, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79165 q = 1) (hb : d88549 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79166 q = 1) (hb : d88550 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79166, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79166, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79167 q = 1) (hb : d88551 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79167, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79167, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79168 q = 1) (hb : d88552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79168, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79168, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25542 (p : Pattern) (ha : d79176 p = 1) (hb : d88568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11271 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11272 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11272, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11273 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11273, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11279 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11279, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52614 q = 1) (hb : d88567 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79176 q = 1) (hb : d88568 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79176, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79176, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25543 (p : Pattern) (ha : d79181 p = 1) (hb : d88574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79177 q = 1) (hb : d88569 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79177, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25542 q ha hb
    | true =>
      simp only [d79177, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79178 q = 1) (hb : d88570 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79178, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79178, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79178 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79178 q = 1) (hb : d88571 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79179 q = 1) (hb : d88572 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79179, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79179, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79180 q = 1) (hb : d88573 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79180, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79180, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79181 q = 1) (hb : d88574 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79181, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79181, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25544 (p : Pattern) (ha : d140179 p = 1) (hb : d140480 p = 1) : d140841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140174 q = 1) (hb : d140465 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140174, d140465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25541 q ha hb
    | true =>
      simp only [d140174, d140465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25543 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79182 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140175 q = 1) (hb : d140466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140175, d140466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140175, d140466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140476 q = 1) : d140476 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140176 q = 1) (hb : d140477 q = 1) : d140838 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140176, d140477, d140838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140176, d140477, d140838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140177 q = 1) (hb : d140478 q = 1) : d140839 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140177, d140478, d140839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140177, d140478, d140839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140178 q = 1) (hb : d140479 q = 1) : d140840 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140178, d140479, d140840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140178, d140479, d140840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140179 q = 1) (hb : d140480 q = 1) : d140841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140179, d140480, d140841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140179, d140480, d140841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25545 (p : Pattern) (ha : d140185 p = 1) (hb : d140486 p = 1) : d140847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79083 q = 1) (hb : d88457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79083, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79083, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25526 q ha hb
  have h2 (q : Pattern) (ha : d79084 q = 1) (hb : d88458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79084, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79084, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79092 q = 1) (hb : d88466 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79092, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25526 q ha hb
    | true =>
      simp only [d79092, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25528 q ha hb
  have h4 (q : Pattern) (ha : d79093 q = 1) (hb : d88467 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79093, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79093, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79094 q = 1) (hb : d88468 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79094, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79094, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140160 q = 1) (hb : d140451 q = 1) : d140828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140160, d140451, d140828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25533 q ha hb
    | true =>
      simp only [d140160, d140451, d140828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25537 q ha hb
  have h7 (q : Pattern) (ha : d140162 q = 1) (hb : d140453 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140162, d140453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25538 q ha hb
    | true =>
      simp only [d140162, d140453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140163 q = 1) (hb : d140454 q = 1) : d140829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140163, d140454, d140829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140163, d140454, d140829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d140164 q = 1) (hb : d140455 q = 1) : d140830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140164, d140455, d140830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140164, d140455, d140830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d140165 q = 1) (hb : d140456 q = 1) : d140831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140165, d140456, d140831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140165, d140456, d140831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140169 q = 1) (hb : d140460 q = 1) : d140833 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140169, d140460, d140833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140169, d140460, d140833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25539 q ha hb
  have h12 (q : Pattern) (ha : d140170 q = 1) (hb : d140461 q = 1) : d140834 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140170, d140461, d140834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d140170, d140461, d140834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d140171 q = 1) (hb : d140462 q = 1) : d140835 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140171, d140462, d140835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d140171, d140462, d140835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d140172 q = 1) (hb : d140463 q = 1) : d140836 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140172, d140463, d140836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d140172, d140463, d140836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d140173 q = 1) (hb : d140464 q = 1) : d140837 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140173, d140464, d140837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140173, d140464, d140837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d140180 q = 1) (hb : d140481 q = 1) : d140842 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140180, d140481, d140842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140180, d140481, d140842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25544 q ha hb
  have h17 (q : Pattern) (ha : d140181 q = 1) (hb : d140482 q = 1) : d140843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140181, d140482, d140843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d140181, d140482, d140843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d140182 q = 1) (hb : d140483 q = 1) : d140844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140182, d140483, d140844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d140182, d140483, d140844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d140183 q = 1) (hb : d140484 q = 1) : d140845 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140183, d140484, d140845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140183, d140484, d140845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d140184 q = 1) (hb : d140485 q = 1) : d140846 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140184, d140485, d140846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d140184, d140485, d140846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d140185 q = 1) (hb : d140486 q = 1) : d140847 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140185, d140486, d140847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140185, d140486, d140847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25546 (p : Pattern) (ha : d140191 p = 1) (hb : d140492 p = 1) : d140853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140186 q = 1) (hb : d140487 q = 1) : d140848 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140186, d140487, d140848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140186, d140487, d140848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25545 q ha hb
  have h2 (q : Pattern) (ha : d140187 q = 1) (hb : d140488 q = 1) : d140849 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140187, d140488, d140849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140187, d140488, d140849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140188 q = 1) (hb : d140489 q = 1) : d140850 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140188, d140489, d140850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140188, d140489, d140850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140189 q = 1) (hb : d140490 q = 1) : d140851 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140189, d140490, d140851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140189, d140490, d140851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140190 q = 1) (hb : d140491 q = 1) : d140852 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140190, d140491, d140852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140190, d140491, d140852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140191 q = 1) (hb : d140492 q = 1) : d140853 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140191, d140492, d140853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140191, d140492, d140853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25547 (p : Pattern) (ha : d79203 p = 1) (hb : d88596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11373 q = 1) (hb : d52727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11373, d52727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52727 q = 1) (hb : d88595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79203 q = 1) (hb : d88596 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79203, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79203, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25548 (p : Pattern) (ha : d79208 p = 1) (hb : d88602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79204 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25547 q ha hb
    | true =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79205 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79207 q = 1) (hb : d88601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79207, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79207, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79208 q = 1) (hb : d88602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79208, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79208, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25549 (p : Pattern) (ha : d79214 p = 1) (hb : d88608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79209 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
    | true =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79210 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79210, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79210, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79211 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79211, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79211, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79212 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79212, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79212, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79213 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79213, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79213, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79214 q = 1) (hb : d88608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79214, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79214, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25550 (p : Pattern) (ha : d79217 p = 1) (hb : d88611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79204 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25547 q ha hb
    | true =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79205 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79207 q = 1) (hb : d88601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79207, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79207, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79217 q = 1) (hb : d88611 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79217, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79217, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25551 (p : Pattern) (ha : d79223 p = 1) (hb : d88617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79209 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
    | true =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79210 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79210, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79210, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79211 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79211, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79211, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79212 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79212, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79212, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79213 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79213, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79213, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79218 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25550 q ha hb
    | true =>
      simp only [d79218, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79219 q = 1) (hb : d88613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79219, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79219, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79220 q = 1) (hb : d88614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79220, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79220, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79221 q = 1) (hb : d88615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79221, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79221, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79222 q = 1) (hb : d88616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79222, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79222, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79223 q = 1) (hb : d88617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79223, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79223, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25552 (p : Pattern) (ha : d79228 p = 1) (hb : d88622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79204 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25547 q ha hb
    | true =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79205 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79227 q = 1) (hb : d88621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79227, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79227, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79228 q = 1) (hb : d88622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79228, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79228, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25553 (p : Pattern) (ha : d79235 p = 1) (hb : d88629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79204 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25547 q ha hb
    | true =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79205 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79233 q = 1) (hb : d88627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79233, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79233, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79234 q = 1) (hb : d88628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79234, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79234, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79235 q = 1) (hb : d88629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79235, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79235, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25554 (p : Pattern) (ha : d79239 p = 1) (hb : d88634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11366 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11367 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11368 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11372 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52726 q = 1) (hb : d88633 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79239 q = 1) (hb : d88634 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79239, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79239, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25555 (p : Pattern) (ha : d79244 p = 1) (hb : d88640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79240 q = 1) (hb : d88635 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79240, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25554 q ha hb
    | true =>
      simp only [d79240, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79241 q = 1) (hb : d88636 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79241, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79241, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79241 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79241 q = 1) (hb : d88637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79242 q = 1) (hb : d88638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79242, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79242, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79243 q = 1) (hb : d88639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79243, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79243, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79244 q = 1) (hb : d88640 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79244, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79244, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25556 (p : Pattern) (ha : d140199 p = 1) (hb : d140510 p = 1) : d140859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79229 q = 1) (hb : d88623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79229, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25552 q ha hb
    | true =>
      simp only [d79229, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79230 q = 1) (hb : d88624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79230, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79230, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79231 q = 1) (hb : d88625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79231, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79231, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79232 q = 1) (hb : d88626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79232, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79232, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79236 q = 1) (hb : d88630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79236, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25553 q ha hb
    | true =>
      simp only [d79236, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79237 q = 1) (hb : d88631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79237, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79237, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79238 q = 1) (hb : d88632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79238, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79238, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140194 q = 1) (hb : d140495 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140194, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25555 q ha hb
    | true =>
      simp only [d140194, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79209 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140195 q = 1) (hb : d140496 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140195, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140195, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140506 q = 1) : d140506 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140196 q = 1) (hb : d140507 q = 1) : d140856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140196, d140507, d140856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140196, d140507, d140856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140197 q = 1) (hb : d140508 q = 1) : d140857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140197, d140508, d140857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140197, d140508, d140857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140198 q = 1) (hb : d140509 q = 1) : d140858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140198, d140509, d140858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140198, d140509, d140858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d140199 q = 1) (hb : d140510 q = 1) : d140859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140199, d140510, d140859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140199, d140510, d140859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25557 (p : Pattern) (ha : d79258 p = 1) (hb : d88660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79204 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25547 q ha hb
    | true =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79205 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79206 q = 1) (hb : d88600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79206, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79227 q = 1) (hb : d88621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79227, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79227, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79258 q = 1) (hb : d88660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79258, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79258, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25558 (p : Pattern) (ha : d79263 p = 1) (hb : d88665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79204 q = 1) (hb : d88597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25547 q ha hb
    | true =>
      simp only [d79204, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79205 q = 1) (hb : d88598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79205, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79205 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79205 q = 1) (hb : d88599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79233 q = 1) (hb : d88627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79233, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79233, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79234 q = 1) (hb : d88628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79234, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79234, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79263 q = 1) (hb : d88665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79263, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79263, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25559 (p : Pattern) (ha : d79267 p = 1) (hb : d88669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79240 q = 1) (hb : d88635 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79240, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25554 q ha hb
    | true =>
      simp only [d79240, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79241 q = 1) (hb : d88636 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79241, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79241, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79241 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79241 q = 1) (hb : d88637 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79242 q = 1) (hb : d88638 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79242, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79242, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79243 q = 1) (hb : d88639 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79243, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79243, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79267 q = 1) (hb : d88669 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79267, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79267, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25560 (p : Pattern) (ha : d140205 p = 1) (hb : d140519 p = 1) : d140863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79229 q = 1) (hb : d88623 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79229, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25552 q ha hb
    | true =>
      simp only [d79229, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79230 q = 1) (hb : d88624 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79230, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79230, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79231 q = 1) (hb : d88625 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79231, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79231, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79232 q = 1) (hb : d88626 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79232, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79232, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79236 q = 1) (hb : d88630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79236, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25553 q ha hb
    | true =>
      simp only [d79236, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79237 q = 1) (hb : d88631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79237, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79237, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79238 q = 1) (hb : d88632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79238, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79238, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140194 q = 1) (hb : d140495 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140194, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25555 q ha hb
    | true =>
      simp only [d140194, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79209 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140195 q = 1) (hb : d140496 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140195, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140195, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140506 q = 1) : d140506 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140196 q = 1) (hb : d140507 q = 1) : d140856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140196, d140507, d140856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140196, d140507, d140856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140197 q = 1) (hb : d140508 q = 1) : d140857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140197, d140508, d140857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140197, d140508, d140857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140198 q = 1) (hb : d140509 q = 1) : d140858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140198, d140509, d140858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140198, d140509, d140858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79259 q = 1) (hb : d88661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79259, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25557 q ha hb
    | true =>
      simp only [d79259, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d79260 q = 1) (hb : d88662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79260, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79260, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79261 q = 1) (hb : d88663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79261, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79261, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79262 q = 1) (hb : d88664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79262, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79262, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79264 q = 1) (hb : d88666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79264, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25558 q ha hb
    | true =>
      simp only [d79264, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79265 q = 1) (hb : d88667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79265, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79265, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79266 q = 1) (hb : d88668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79266, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79266, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d140200 q = 1) (hb : d140511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140200, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25559 q ha hb
    | true =>
      simp only [d140200, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25550 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d79218 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d140201 q = 1) (hb : d140512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140201, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d140201, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d140515 q = 1) : d140515 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d140202 q = 1) (hb : d140516 q = 1) : d140860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140202, d140516, d140860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d140202, d140516, d140860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d140203 q = 1) (hb : d140517 q = 1) : d140861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140203, d140517, d140861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d140203, d140517, d140861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d140204 q = 1) (hb : d140518 q = 1) : d140862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140204, d140518, d140862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140204, d140518, d140862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d140205 q = 1) (hb : d140519 q = 1) : d140863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140205, d140519, d140863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d140205, d140519, d140863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25561 (p : Pattern) (ha : d140207 p = 1) (hb : d140521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79209 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
    | true =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79210 q = 1) (hb : d88604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79210, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79210, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79211 q = 1) (hb : d88605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79211, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79211, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79212 q = 1) (hb : d88606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79212, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79212, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79213 q = 1) (hb : d88607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79213, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79213, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140207 q = 1) (hb : d140521 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140207, d140521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140207, d140521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25562 (p : Pattern) (ha : d140214 p = 1) (hb : d140528 p = 1) : d140868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140200 q = 1) (hb : d140511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140200, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25559 q ha hb
    | true =>
      simp only [d140200, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25550 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79218 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140201 q = 1) (hb : d140512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140201, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140201, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140515 q = 1) : d140515 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140202 q = 1) (hb : d140516 q = 1) : d140860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140202, d140516, d140860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140202, d140516, d140860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140212 q = 1) (hb : d140526 q = 1) : d140861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140212, d140526, d140861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140212, d140526, d140861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140213 q = 1) (hb : d140527 q = 1) : d140862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140213, d140527, d140862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140213, d140527, d140862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140214 q = 1) (hb : d140528 q = 1) : d140868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140214, d140528, d140868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140214, d140528, d140868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25563 (p : Pattern) (ha : d79295 p = 1) (hb : d88698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11537 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11538 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11539 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11544 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52903 q = 1) (hb : d88697 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79295 q = 1) (hb : d88698 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79295, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79295, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25564 (p : Pattern) (ha : d79300 p = 1) (hb : d88704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79296 q = 1) (hb : d88699 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79296, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25563 q ha hb
    | true =>
      simp only [d79296, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79297 q = 1) (hb : d88700 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79297, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79297, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79297 q = 1) (hb : d88701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79298 q = 1) (hb : d88702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79298, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79298, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79299 q = 1) (hb : d88703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79299, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79299, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79300 q = 1) (hb : d88704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79300, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79300, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25565 (p : Pattern) (ha : d79308 p = 1) (hb : d88720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11549 q = 1) (hb : d52908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11549, d52908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52908 q = 1) (hb : d88719 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79308 q = 1) (hb : d88720 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79308, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79308, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25566 (p : Pattern) (ha : d79313 p = 1) (hb : d88726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79309 q = 1) (hb : d88721 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79309, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25565 q ha hb
    | true =>
      simp only [d79309, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79310 q = 1) (hb : d88722 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79310, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79310, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79310 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79310 q = 1) (hb : d88723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79311 q = 1) (hb : d88724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79311, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79311, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79312 q = 1) (hb : d88725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79312, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79312, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79313 q = 1) (hb : d88726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79313, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79313, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25567 (p : Pattern) (ha : d140225 p = 1) (hb : d140549 p = 1) : d140877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140220 q = 1) (hb : d140534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140220, d140534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25564 q ha hb
    | true =>
      simp only [d140220, d140534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25566 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140221 q = 1) (hb : d140535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140221, d140535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140221, d140535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140545 q = 1) : d140545 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140222 q = 1) (hb : d140546 q = 1) : d140874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140222, d140546, d140874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140222, d140546, d140874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140223 q = 1) (hb : d140547 q = 1) : d140875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140223, d140547, d140875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140223, d140547, d140875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140224 q = 1) (hb : d140548 q = 1) : d140876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140224, d140548, d140876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140224, d140548, d140876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140225 q = 1) (hb : d140549 q = 1) : d140877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140225, d140549, d140877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140225, d140549, d140877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25568 (p : Pattern) (ha : d140231 p = 1) (hb : d140555 p = 1) : d140883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79215 q = 1) (hb : d88609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79215, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79215, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25549 q ha hb
  have h2 (q : Pattern) (ha : d79216 q = 1) (hb : d88610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79216, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79216, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79224 q = 1) (hb : d88618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79224, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25549 q ha hb
    | true =>
      simp only [d79224, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25551 q ha hb
  have h4 (q : Pattern) (ha : d79225 q = 1) (hb : d88619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79225, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79225, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79226 q = 1) (hb : d88620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79226, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79226, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140206 q = 1) (hb : d140520 q = 1) : d140864 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140206, d140520, d140864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25556 q ha hb
    | true =>
      simp only [d140206, d140520, d140864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25560 q ha hb
  have h7 (q : Pattern) (ha : d140208 q = 1) (hb : d140522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140208, d140522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25561 q ha hb
    | true =>
      simp only [d140208, d140522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140209 q = 1) (hb : d140523 q = 1) : d140865 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140209, d140523, d140865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140209, d140523, d140865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d140210 q = 1) (hb : d140524 q = 1) : d140866 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140210, d140524, d140866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140210, d140524, d140866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d140211 q = 1) (hb : d140525 q = 1) : d140867 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140211, d140525, d140867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140211, d140525, d140867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140215 q = 1) (hb : d140529 q = 1) : d140869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140215, d140529, d140869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140215, d140529, d140869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25562 q ha hb
  have h12 (q : Pattern) (ha : d140216 q = 1) (hb : d140530 q = 1) : d140870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140216, d140530, d140870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d140216, d140530, d140870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d140217 q = 1) (hb : d140531 q = 1) : d140871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140217, d140531, d140871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d140217, d140531, d140871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d140218 q = 1) (hb : d140532 q = 1) : d140872 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140218, d140532, d140872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d140218, d140532, d140872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d140219 q = 1) (hb : d140533 q = 1) : d140873 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140219, d140533, d140873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140219, d140533, d140873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d140226 q = 1) (hb : d140550 q = 1) : d140878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140226, d140550, d140878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140226, d140550, d140878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25567 q ha hb
  have h17 (q : Pattern) (ha : d140227 q = 1) (hb : d140551 q = 1) : d140879 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140227, d140551, d140879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d140227, d140551, d140879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d140228 q = 1) (hb : d140552 q = 1) : d140880 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140228, d140552, d140880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d140228, d140552, d140880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d140229 q = 1) (hb : d140553 q = 1) : d140881 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140229, d140553, d140881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140229, d140553, d140881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d140230 q = 1) (hb : d140554 q = 1) : d140882 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140230, d140554, d140882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d140230, d140554, d140882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d140231 q = 1) (hb : d140555 q = 1) : d140883 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140231, d140555, d140883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140231, d140555, d140883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25569 (p : Pattern) (ha : d140237 p = 1) (hb : d140561 p = 1) : d140889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140232 q = 1) (hb : d140556 q = 1) : d140884 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140232, d140556, d140884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140232, d140556, d140884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25568 q ha hb
  have h2 (q : Pattern) (ha : d140233 q = 1) (hb : d140557 q = 1) : d140885 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140233, d140557, d140885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140233, d140557, d140885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140234 q = 1) (hb : d140558 q = 1) : d140886 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140234, d140558, d140886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140234, d140558, d140886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140235 q = 1) (hb : d140559 q = 1) : d140887 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140235, d140559, d140887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140235, d140559, d140887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140236 q = 1) (hb : d140560 q = 1) : d140888 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140236, d140560, d140888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140236, d140560, d140888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140237 q = 1) (hb : d140561 q = 1) : d140889 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140237, d140561, d140889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140237, d140561, d140889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25570 (p : Pattern) (ha : d79336 p = 1) (hb : d88749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11644 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11644, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53048 q = 1) (hb : d88748 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79336 q = 1) (hb : d88749 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79336, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79336, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25571 (p : Pattern) (ha : d79341 p = 1) (hb : d88755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79337 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25570 q ha hb
    | true =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79338 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79340 q = 1) (hb : d88754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79340, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79340, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79341 q = 1) (hb : d88755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79341, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79341, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25572 (p : Pattern) (ha : d79347 p = 1) (hb : d88761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79342 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
    | true =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79343 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79343, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79343, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79344 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79344, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79344, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79345 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79345, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79345, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79346 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79346, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79346, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79347 q = 1) (hb : d88761 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79347, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79347, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25573 (p : Pattern) (ha : d79350 p = 1) (hb : d88764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79337 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25570 q ha hb
    | true =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79338 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79340 q = 1) (hb : d88754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79340, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79340, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79350 q = 1) (hb : d88764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79350, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79350, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25574 (p : Pattern) (ha : d79356 p = 1) (hb : d88770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79342 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
    | true =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79343 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79343, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79343, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79344 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79344, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79344, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79345 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79345, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79345, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79346 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79346, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79346, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79351 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25573 q ha hb
    | true =>
      simp only [d79351, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79352 q = 1) (hb : d88766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79352, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79352, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79353 q = 1) (hb : d88767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79353, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79353, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79354 q = 1) (hb : d88768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79354, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79354, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79355 q = 1) (hb : d88769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79355, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79355, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79356 q = 1) (hb : d88770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79356, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79356, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25575 (p : Pattern) (ha : d79361 p = 1) (hb : d88775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79337 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25570 q ha hb
    | true =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79338 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79360 q = 1) (hb : d88774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79360, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79360, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79361 q = 1) (hb : d88775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79361, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79361, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25576 (p : Pattern) (ha : d79368 p = 1) (hb : d88782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79337 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25570 q ha hb
    | true =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79338 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79366 q = 1) (hb : d88780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79366, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79366, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79367 q = 1) (hb : d88781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79367, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79367, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79368 q = 1) (hb : d88782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79368, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79368, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25577 (p : Pattern) (ha : d79372 p = 1) (hb : d88787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11637 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11638 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11639 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11643 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53047 q = 1) (hb : d88786 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79372 q = 1) (hb : d88787 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79372, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79372, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25578 (p : Pattern) (ha : d79377 p = 1) (hb : d88793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79373 q = 1) (hb : d88788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79373, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25577 q ha hb
    | true =>
      simp only [d79373, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79374 q = 1) (hb : d88789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79374, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79374, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79374 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79374 q = 1) (hb : d88790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79375 q = 1) (hb : d88791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79375, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79375, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79376 q = 1) (hb : d88792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79376, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79376, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79377 q = 1) (hb : d88793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79377, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79377, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25579 (p : Pattern) (ha : d140246 p = 1) (hb : d140580 p = 1) : d140896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79362 q = 1) (hb : d88776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79362, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25575 q ha hb
    | true =>
      simp only [d79362, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79363 q = 1) (hb : d88777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79363, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79363, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79364 q = 1) (hb : d88778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79364, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79364, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79365 q = 1) (hb : d88779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79365, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79365, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79369 q = 1) (hb : d88783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79369, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25576 q ha hb
    | true =>
      simp only [d79369, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79370 q = 1) (hb : d88784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79370, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79370, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79371 q = 1) (hb : d88785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79371, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79371, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140241 q = 1) (hb : d140565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140241, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25578 q ha hb
    | true =>
      simp only [d140241, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79342 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140242 q = 1) (hb : d140566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140242, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140242, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140576 q = 1) : d140576 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140243 q = 1) (hb : d140577 q = 1) : d140893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140243, d140577, d140893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140243, d140577, d140893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140244 q = 1) (hb : d140578 q = 1) : d140894 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140244, d140578, d140894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140244, d140578, d140894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140245 q = 1) (hb : d140579 q = 1) : d140895 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140245, d140579, d140895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140245, d140579, d140895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d140246 q = 1) (hb : d140580 q = 1) : d140896 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140246, d140580, d140896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140246, d140580, d140896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25580 (p : Pattern) (ha : d79391 p = 1) (hb : d88813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79337 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25570 q ha hb
    | true =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79338 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79339 q = 1) (hb : d88753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79339, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79360 q = 1) (hb : d88774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79360, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79360, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79391 q = 1) (hb : d88813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79391, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79391, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25581 (p : Pattern) (ha : d79396 p = 1) (hb : d88818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79337 q = 1) (hb : d88750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25570 q ha hb
    | true =>
      simp only [d79337, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79338 q = 1) (hb : d88751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79338, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79338 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79338 q = 1) (hb : d88752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79366 q = 1) (hb : d88780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79366, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79366, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79367 q = 1) (hb : d88781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79367, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79367, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79396 q = 1) (hb : d88818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79396, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79396, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25582 (p : Pattern) (ha : d79400 p = 1) (hb : d88822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79373 q = 1) (hb : d88788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79373, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25577 q ha hb
    | true =>
      simp only [d79373, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79374 q = 1) (hb : d88789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79374, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79374, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79374 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79374 q = 1) (hb : d88790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79375 q = 1) (hb : d88791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79375, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79375, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79376 q = 1) (hb : d88792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79376, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79376, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79400 q = 1) (hb : d88822 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79400, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79400, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25583 (p : Pattern) (ha : d140252 p = 1) (hb : d140589 p = 1) : d140900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79362 q = 1) (hb : d88776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79362, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25575 q ha hb
    | true =>
      simp only [d79362, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79363 q = 1) (hb : d88777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79363, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79363, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79364 q = 1) (hb : d88778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79364, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79364, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79365 q = 1) (hb : d88779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79365, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79365, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79369 q = 1) (hb : d88783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79369, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25576 q ha hb
    | true =>
      simp only [d79369, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79370 q = 1) (hb : d88784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79370, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79370, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79371 q = 1) (hb : d88785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79371, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79371, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140241 q = 1) (hb : d140565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140241, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25578 q ha hb
    | true =>
      simp only [d140241, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79342 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140242 q = 1) (hb : d140566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140242, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140242, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140576 q = 1) : d140576 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140243 q = 1) (hb : d140577 q = 1) : d140893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140243, d140577, d140893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140243, d140577, d140893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140244 q = 1) (hb : d140578 q = 1) : d140894 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140244, d140578, d140894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140244, d140578, d140894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140245 q = 1) (hb : d140579 q = 1) : d140895 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140245, d140579, d140895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140245, d140579, d140895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79392 q = 1) (hb : d88814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79392, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25580 q ha hb
    | true =>
      simp only [d79392, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d79393 q = 1) (hb : d88815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79393, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79393, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79394 q = 1) (hb : d88816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79394, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79394, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79395 q = 1) (hb : d88817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79395, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79395, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79397 q = 1) (hb : d88819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79397, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25581 q ha hb
    | true =>
      simp only [d79397, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79398 q = 1) (hb : d88820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79398, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79398, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79399 q = 1) (hb : d88821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79399, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79399, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d140247 q = 1) (hb : d140581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140247, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25582 q ha hb
    | true =>
      simp only [d140247, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25573 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d79351 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d140248 q = 1) (hb : d140582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140248, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d140248, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d140585 q = 1) : d140585 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d140249 q = 1) (hb : d140586 q = 1) : d140897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140249, d140586, d140897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d140249, d140586, d140897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d140250 q = 1) (hb : d140587 q = 1) : d140898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140250, d140587, d140898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d140250, d140587, d140898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d140251 q = 1) (hb : d140588 q = 1) : d140899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140251, d140588, d140899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140251, d140588, d140899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d140252 q = 1) (hb : d140589 q = 1) : d140900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140252, d140589, d140900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d140252, d140589, d140900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25584 (p : Pattern) (ha : d140254 p = 1) (hb : d140591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79342 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
    | true =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79343 q = 1) (hb : d88757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79343, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79343, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79344 q = 1) (hb : d88758 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79344, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79344, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79345 q = 1) (hb : d88759 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79345, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79345, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79346 q = 1) (hb : d88760 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79346, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79346, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140254 q = 1) (hb : d140591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140254, d140591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140254, d140591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25585 (p : Pattern) (ha : d140261 p = 1) (hb : d140598 p = 1) : d140905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140247 q = 1) (hb : d140581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140247, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25582 q ha hb
    | true =>
      simp only [d140247, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25573 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140248 q = 1) (hb : d140582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140248, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140248, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140585 q = 1) : d140585 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140249 q = 1) (hb : d140586 q = 1) : d140897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140249, d140586, d140897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140249, d140586, d140897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140259 q = 1) (hb : d140596 q = 1) : d140898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140259, d140596, d140898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140259, d140596, d140898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140260 q = 1) (hb : d140597 q = 1) : d140899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140260, d140597, d140899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140260, d140597, d140899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140261 q = 1) (hb : d140598 q = 1) : d140905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140261, d140598, d140905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140261, d140598, d140905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25586 (p : Pattern) (ha : d79428 p = 1) (hb : d88851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11808 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11809 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11810 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11815 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53218 q = 1) (hb : d88850 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79428 q = 1) (hb : d88851 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79428, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79428, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25587 (p : Pattern) (ha : d79433 p = 1) (hb : d88857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79429 q = 1) (hb : d88852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79429, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25586 q ha hb
    | true =>
      simp only [d79429, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79430 q = 1) (hb : d88853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79430, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79430, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79430 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79430 q = 1) (hb : d88854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79431 q = 1) (hb : d88855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79431, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79431, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79432 q = 1) (hb : d88856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79432, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79432, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79433 q = 1) (hb : d88857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79433, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79433, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25588 (p : Pattern) (ha : d79441 p = 1) (hb : d88873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11820 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11820, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53223 q = 1) (hb : d88872 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79441 q = 1) (hb : d88873 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79441, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79441, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25589 (p : Pattern) (ha : d79446 p = 1) (hb : d88879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79442 q = 1) (hb : d88874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79442, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25588 q ha hb
    | true =>
      simp only [d79442, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79443 q = 1) (hb : d88875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79443, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79443, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79443 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79443 q = 1) (hb : d88876 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79444 q = 1) (hb : d88877 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79444, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79444, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79445 q = 1) (hb : d88878 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79445, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79445, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79446 q = 1) (hb : d88879 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79446, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79446, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25590 (p : Pattern) (ha : d140272 p = 1) (hb : d140619 p = 1) : d140914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140267 q = 1) (hb : d140604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140267, d140604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25587 q ha hb
    | true =>
      simp only [d140267, d140604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25589 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79447 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140268 q = 1) (hb : d140605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140268, d140605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140268, d140605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140615 q = 1) : d140615 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140269 q = 1) (hb : d140616 q = 1) : d140911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140269, d140616, d140911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140269, d140616, d140911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140270 q = 1) (hb : d140617 q = 1) : d140912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140270, d140617, d140912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140270, d140617, d140912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140271 q = 1) (hb : d140618 q = 1) : d140913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140271, d140618, d140913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140271, d140618, d140913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140272 q = 1) (hb : d140619 q = 1) : d140914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140272, d140619, d140914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140272, d140619, d140914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25591 (p : Pattern) (ha : d140278 p = 1) (hb : d140625 p = 1) : d140920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79348 q = 1) (hb : d88762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79348, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79348, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25572 q ha hb
  have h2 (q : Pattern) (ha : d79349 q = 1) (hb : d88763 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79349, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79349, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79357 q = 1) (hb : d88771 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79357, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25572 q ha hb
    | true =>
      simp only [d79357, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25574 q ha hb
  have h4 (q : Pattern) (ha : d79358 q = 1) (hb : d88772 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79358, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79358, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79359 q = 1) (hb : d88773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79359, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79359, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140253 q = 1) (hb : d140590 q = 1) : d140901 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140253, d140590, d140901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25579 q ha hb
    | true =>
      simp only [d140253, d140590, d140901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25583 q ha hb
  have h7 (q : Pattern) (ha : d140255 q = 1) (hb : d140592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140255, d140592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25584 q ha hb
    | true =>
      simp only [d140255, d140592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140256 q = 1) (hb : d140593 q = 1) : d140902 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140256, d140593, d140902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140256, d140593, d140902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d140257 q = 1) (hb : d140594 q = 1) : d140903 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140257, d140594, d140903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140257, d140594, d140903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d140258 q = 1) (hb : d140595 q = 1) : d140904 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140258, d140595, d140904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140258, d140595, d140904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140262 q = 1) (hb : d140599 q = 1) : d140906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140262, d140599, d140906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140262, d140599, d140906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25585 q ha hb
  have h12 (q : Pattern) (ha : d140263 q = 1) (hb : d140600 q = 1) : d140907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140263, d140600, d140907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d140263, d140600, d140907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d140264 q = 1) (hb : d140601 q = 1) : d140908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140264, d140601, d140908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d140264, d140601, d140908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d140265 q = 1) (hb : d140602 q = 1) : d140909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140265, d140602, d140909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d140265, d140602, d140909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d140266 q = 1) (hb : d140603 q = 1) : d140910 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140266, d140603, d140910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140266, d140603, d140910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d140273 q = 1) (hb : d140620 q = 1) : d140915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140273, d140620, d140915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140273, d140620, d140915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25590 q ha hb
  have h17 (q : Pattern) (ha : d140274 q = 1) (hb : d140621 q = 1) : d140916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140274, d140621, d140916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d140274, d140621, d140916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d140275 q = 1) (hb : d140622 q = 1) : d140917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140275, d140622, d140917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d140275, d140622, d140917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d140276 q = 1) (hb : d140623 q = 1) : d140918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140276, d140623, d140918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140276, d140623, d140918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d140277 q = 1) (hb : d140624 q = 1) : d140919 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140277, d140624, d140919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d140277, d140624, d140919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d140278 q = 1) (hb : d140625 q = 1) : d140920 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140278, d140625, d140920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140278, d140625, d140920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25592 (p : Pattern) (ha : d140284 p = 1) (hb : d140631 p = 1) : d140926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140279 q = 1) (hb : d140626 q = 1) : d140921 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140279, d140626, d140921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140279, d140626, d140921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25591 q ha hb
  have h2 (q : Pattern) (ha : d140280 q = 1) (hb : d140627 q = 1) : d140922 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140280, d140627, d140922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140280, d140627, d140922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140281 q = 1) (hb : d140628 q = 1) : d140923 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140281, d140628, d140923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140281, d140628, d140923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140282 q = 1) (hb : d140629 q = 1) : d140924 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140282, d140629, d140924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140282, d140629, d140924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140283 q = 1) (hb : d140630 q = 1) : d140925 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140283, d140630, d140925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140283, d140630, d140925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140284 q = 1) (hb : d140631 q = 1) : d140926 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140284, d140631, d140926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140284, d140631, d140926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25593 (p : Pattern) (ha : d79470 p = 1) (hb : d88903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11916 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11916, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53369 q = 1) (hb : d88902 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79470 q = 1) (hb : d88903 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79470, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79470, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25594 (p : Pattern) (ha : d79475 p = 1) (hb : d88909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79471 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25593 q ha hb
    | true =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79472 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79474 q = 1) (hb : d88908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79474, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79474, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79475 q = 1) (hb : d88909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79475, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79475, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25595 (p : Pattern) (ha : d79481 p = 1) (hb : d88915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79476 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
    | true =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79477 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79477, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79477, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79478 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79478, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79478, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79479 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79479, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79479, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79480 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79480, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79480, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79481 q = 1) (hb : d88915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79481, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79481, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25596 (p : Pattern) (ha : d79484 p = 1) (hb : d88918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79471 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25593 q ha hb
    | true =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79472 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79474 q = 1) (hb : d88908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79474, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79474, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79484 q = 1) (hb : d88918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79484, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79484, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25597 (p : Pattern) (ha : d79490 p = 1) (hb : d88924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79476 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
    | true =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79477 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79477, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79477, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79478 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79478, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79478, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79479 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79479, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79479, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79480 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79480, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79480, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79485 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25596 q ha hb
    | true =>
      simp only [d79485, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79486 q = 1) (hb : d88920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79486, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79486, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79487 q = 1) (hb : d88921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79487, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79487, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d79488 q = 1) (hb : d88922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79488, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79488, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79489 q = 1) (hb : d88923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79489, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79489, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d79490 q = 1) (hb : d88924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79490, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79490, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25598 (p : Pattern) (ha : d79495 p = 1) (hb : d88929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79471 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25593 q ha hb
    | true =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79472 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79494 q = 1) (hb : d88928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79494, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79494, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79495 q = 1) (hb : d88929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79495, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79495, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25599 (p : Pattern) (ha : d79502 p = 1) (hb : d88936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79471 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25593 q ha hb
    | true =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79472 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79500 q = 1) (hb : d88934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79500, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79500, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79501 q = 1) (hb : d88935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79501, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79501, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79502 q = 1) (hb : d88936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79502, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79502, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25600 (p : Pattern) (ha : d79506 p = 1) (hb : d88941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11909 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11910 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11911 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11915 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53368 q = 1) (hb : d88940 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79506 q = 1) (hb : d88941 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79506, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79506, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25601 (p : Pattern) (ha : d79511 p = 1) (hb : d88947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79507 q = 1) (hb : d88942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79507, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25600 q ha hb
    | true =>
      simp only [d79507, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79508 q = 1) (hb : d88943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79508, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79508, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79508 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79508 q = 1) (hb : d88944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79509 q = 1) (hb : d88945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79509, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79509, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79510 q = 1) (hb : d88946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79510, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79510, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79511 q = 1) (hb : d88947 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79511, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79511, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25602 (p : Pattern) (ha : d140294 p = 1) (hb : d140651 p = 1) : d140934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79496 q = 1) (hb : d88930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79496, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25598 q ha hb
    | true =>
      simp only [d79496, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79497 q = 1) (hb : d88931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79497, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79497, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79498 q = 1) (hb : d88932 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79498, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79498, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79499 q = 1) (hb : d88933 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79499, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79499, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79503 q = 1) (hb : d88937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79503, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25599 q ha hb
    | true =>
      simp only [d79503, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79504 q = 1) (hb : d88938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79504, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79504, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79505 q = 1) (hb : d88939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79505, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79505, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140289 q = 1) (hb : d140636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140289, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25601 q ha hb
    | true =>
      simp only [d140289, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79476 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140290 q = 1) (hb : d140637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140290, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140290, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140647 q = 1) : d140647 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140291 q = 1) (hb : d140648 q = 1) : d140931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140291, d140648, d140931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140291, d140648, d140931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140292 q = 1) (hb : d140649 q = 1) : d140932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140292, d140649, d140932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140292, d140649, d140932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140293 q = 1) (hb : d140650 q = 1) : d140933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140293, d140650, d140933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140293, d140650, d140933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d140294 q = 1) (hb : d140651 q = 1) : d140934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140294, d140651, d140934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140294, d140651, d140934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25603 (p : Pattern) (ha : d79525 p = 1) (hb : d88967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79471 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25593 q ha hb
    | true =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79472 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79473 q = 1) (hb : d88907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79473, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79494 q = 1) (hb : d88928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79494, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79494, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79525 q = 1) (hb : d88967 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79525, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79525, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25604 (p : Pattern) (ha : d79530 p = 1) (hb : d88972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79471 q = 1) (hb : d88904 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25593 q ha hb
    | true =>
      simp only [d79471, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79472 q = 1) (hb : d88905 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79472, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79472 q = 1) (hb : d88906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79500 q = 1) (hb : d88934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79500, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79500, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d79501 q = 1) (hb : d88935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79501, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79501, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79530 q = 1) (hb : d88972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79530, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79530, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25605 (p : Pattern) (ha : d79534 p = 1) (hb : d88976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79507 q = 1) (hb : d88942 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79507, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25600 q ha hb
    | true =>
      simp only [d79507, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79508 q = 1) (hb : d88943 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79508, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79508, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79508 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79508 q = 1) (hb : d88944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79509 q = 1) (hb : d88945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79509, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79509, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79510 q = 1) (hb : d88946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79510, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79510, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79534 q = 1) (hb : d88976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79534, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79534, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25606 (p : Pattern) (ha : d140300 p = 1) (hb : d140660 p = 1) : d140938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79496 q = 1) (hb : d88930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79496, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25598 q ha hb
    | true =>
      simp only [d79496, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79497 q = 1) (hb : d88931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79497, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79497, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79498 q = 1) (hb : d88932 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79498, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79498, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79499 q = 1) (hb : d88933 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79499, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79499, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79503 q = 1) (hb : d88937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79503, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25599 q ha hb
    | true =>
      simp only [d79503, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79504 q = 1) (hb : d88938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79504, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79504, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79505 q = 1) (hb : d88939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79505, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79505, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140289 q = 1) (hb : d140636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140289, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25601 q ha hb
    | true =>
      simp only [d140289, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79476 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d140290 q = 1) (hb : d140637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140290, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140290, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d140647 q = 1) : d140647 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d140291 q = 1) (hb : d140648 q = 1) : d140931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140291, d140648, d140931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140291, d140648, d140931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140292 q = 1) (hb : d140649 q = 1) : d140932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140292, d140649, d140932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d140292, d140649, d140932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140293 q = 1) (hb : d140650 q = 1) : d140933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140293, d140650, d140933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140293, d140650, d140933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d79526 q = 1) (hb : d88968 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79526, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25603 q ha hb
    | true =>
      simp only [d79526, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d79527 q = 1) (hb : d88969 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79527, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79527, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d79528 q = 1) (hb : d88970 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79528, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d79528, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d79529 q = 1) (hb : d88971 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79529, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79529, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79531 q = 1) (hb : d88973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79531, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25604 q ha hb
    | true =>
      simp only [d79531, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d79532 q = 1) (hb : d88974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79532, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79532, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d79533 q = 1) (hb : d88975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79533, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d79533, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d140295 q = 1) (hb : d140652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140295, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25605 q ha hb
    | true =>
      simp only [d140295, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25596 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d79485 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d140296 q = 1) (hb : d140653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140296, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d140296, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d140656 q = 1) : d140656 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d140297 q = 1) (hb : d140657 q = 1) : d140935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140297, d140657, d140935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d140297, d140657, d140935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d140298 q = 1) (hb : d140658 q = 1) : d140936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140298, d140658, d140936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d140298, d140658, d140936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d140299 q = 1) (hb : d140659 q = 1) : d140937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140299, d140659, d140937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140299, d140659, d140937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d140300 q = 1) (hb : d140660 q = 1) : d140938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140300, d140660, d140938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d140300, d140660, d140938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25607 (p : Pattern) (ha : d140302 p = 1) (hb : d140662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79476 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
    | true =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79477 q = 1) (hb : d88911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79477, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79477, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79478 q = 1) (hb : d88912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79478, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79478, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d79479 q = 1) (hb : d88913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79479, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79479, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79480 q = 1) (hb : d88914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79480, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79480, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140302 q = 1) (hb : d140662 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140302, d140662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140302, d140662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25608 (p : Pattern) (ha : d140309 p = 1) (hb : d140669 p = 1) : d140943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140295 q = 1) (hb : d140652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140295, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25605 q ha hb
    | true =>
      simp only [d140295, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25596 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79485 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140296 q = 1) (hb : d140653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140296, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140296, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140656 q = 1) : d140656 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140297 q = 1) (hb : d140657 q = 1) : d140935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140297, d140657, d140935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140297, d140657, d140935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140307 q = 1) (hb : d140667 q = 1) : d140936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140307, d140667, d140936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140307, d140667, d140936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140308 q = 1) (hb : d140668 q = 1) : d140937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140308, d140668, d140937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140308, d140668, d140937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140309 q = 1) (hb : d140669 q = 1) : d140943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140309, d140669, d140943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140309, d140669, d140943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25609 (p : Pattern) (ha : d79562 p = 1) (hb : d89005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12080 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12081 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12082 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12087 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53535 q = 1) (hb : d89004 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d79562 q = 1) (hb : d89005 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79562, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79562, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro25610 (p : Pattern) (ha : d79567 p = 1) (hb : d89011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79563 q = 1) (hb : d89006 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79563, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25609 q ha hb
    | true =>
      simp only [d79563, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79564 q = 1) (hb : d89007 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79564, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79564, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79564 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79564 q = 1) (hb : d89008 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79565 q = 1) (hb : d89009 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79565, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79565, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79566 q = 1) (hb : d89010 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79566, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79566, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79567 q = 1) (hb : d89011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79567, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79567, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25611 (p : Pattern) (ha : d79575 p = 1) (hb : d89027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12092 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12092, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53540 q = 1) (hb : d89026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d79575 q = 1) (hb : d89027 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d79575, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d79575, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro25612 (p : Pattern) (ha : d79580 p = 1) (hb : d89033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79576 q = 1) (hb : d89028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d79576, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25611 q ha hb
    | true =>
      simp only [d79576, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d79577 q = 1) (hb : d89029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79577, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79577, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79577 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79577 q = 1) (hb : d89030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79578 q = 1) (hb : d89031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79578, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79578, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d79579 q = 1) (hb : d89032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79579, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79579, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d79580 q = 1) (hb : d89033 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79580, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79580, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25613 (p : Pattern) (ha : d140320 p = 1) (hb : d140690 p = 1) : d140952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140315 q = 1) (hb : d140675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d140315, d140675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25610 q ha hb
    | true =>
      simp only [d140315, d140675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25612 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d140316 q = 1) (hb : d140676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d140316, d140676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140316, d140676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d140686 q = 1) : d140686 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d140317 q = 1) (hb : d140687 q = 1) : d140949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d140317, d140687, d140949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140317, d140687, d140949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140318 q = 1) (hb : d140688 q = 1) : d140950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d140318, d140688, d140950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140318, d140688, d140950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140319 q = 1) (hb : d140689 q = 1) : d140951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d140319, d140689, d140951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140319, d140689, d140951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d140320 q = 1) (hb : d140690 q = 1) : d140952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d140320, d140690, d140952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140320, d140690, d140952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25614 (p : Pattern) (ha : d140326 p = 1) (hb : d140696 p = 1) : d140958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79482 q = 1) (hb : d88916 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79482, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79482, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25595 q ha hb
  have h2 (q : Pattern) (ha : d79483 q = 1) (hb : d88917 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79483, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79483, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d79491 q = 1) (hb : d88925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79491, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25595 q ha hb
    | true =>
      simp only [d79491, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25597 q ha hb
  have h4 (q : Pattern) (ha : d79492 q = 1) (hb : d88926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79492, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79492, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d79493 q = 1) (hb : d88927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d79493, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79493, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140301 q = 1) (hb : d140661 q = 1) : d140939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140301, d140661, d140939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25602 q ha hb
    | true =>
      simp only [d140301, d140661, d140939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25606 q ha hb
  have h7 (q : Pattern) (ha : d140303 q = 1) (hb : d140663 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140303, d140663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25607 q ha hb
    | true =>
      simp only [d140303, d140663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d140304 q = 1) (hb : d140664 q = 1) : d140940 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140304, d140664, d140940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140304, d140664, d140940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d140305 q = 1) (hb : d140665 q = 1) : d140941 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140305, d140665, d140941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140305, d140665, d140941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d140306 q = 1) (hb : d140666 q = 1) : d140942 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140306, d140666, d140942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140306, d140666, d140942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140310 q = 1) (hb : d140670 q = 1) : d140944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140310, d140670, d140944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140310, d140670, d140944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25608 q ha hb
  have h12 (q : Pattern) (ha : d140311 q = 1) (hb : d140671 q = 1) : d140945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140311, d140671, d140945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d140311, d140671, d140945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d140312 q = 1) (hb : d140672 q = 1) : d140946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140312, d140672, d140946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d140312, d140672, d140946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d140313 q = 1) (hb : d140673 q = 1) : d140947 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140313, d140673, d140947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d140313, d140673, d140947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d140314 q = 1) (hb : d140674 q = 1) : d140948 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140314, d140674, d140948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140314, d140674, d140948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d140321 q = 1) (hb : d140691 q = 1) : d140953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d140321, d140691, d140953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140321, d140691, d140953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25613 q ha hb
  have h17 (q : Pattern) (ha : d140322 q = 1) (hb : d140692 q = 1) : d140954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d140322, d140692, d140954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d140322, d140692, d140954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d140323 q = 1) (hb : d140693 q = 1) : d140955 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d140323, d140693, d140955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d140323, d140693, d140955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d140324 q = 1) (hb : d140694 q = 1) : d140956 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d140324, d140694, d140956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d140324, d140694, d140956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d140325 q = 1) (hb : d140695 q = 1) : d140957 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d140325, d140695, d140957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d140325, d140695, d140957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d140326 q = 1) (hb : d140696 q = 1) : d140958 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d140326, d140696, d140958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140326, d140696, d140958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25615 (p : Pattern) (ha : d140332 p = 1) (hb : d140702 p = 1) : d140964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140327 q = 1) (hb : d140697 q = 1) : d140959 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d140327, d140697, d140959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140327, d140697, d140959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25614 q ha hb
  have h2 (q : Pattern) (ha : d140328 q = 1) (hb : d140698 q = 1) : d140960 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d140328, d140698, d140960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140328, d140698, d140960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140329 q = 1) (hb : d140699 q = 1) : d140961 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d140329, d140699, d140961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140329, d140699, d140961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140330 q = 1) (hb : d140700 q = 1) : d140962 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d140330, d140700, d140962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140330, d140700, d140962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140331 q = 1) (hb : d140701 q = 1) : d140963 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d140331, d140701, d140963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140331, d140701, d140963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140332 q = 1) (hb : d140702 q = 1) : d140964 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d140332, d140702, d140964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d140332, d140702, d140964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25616 (p : Pattern) (ha : d140338 p = 1) (hb : d140708 p = 1) : d140970 p = 1 := by
  have h0 (q : Pattern) (ha : d140147 q = 1) (hb : d140425 q = 1) : d140819 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140147, d140425, d140819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25500 q hb ha
    | true =>
      simp only [d140147, d140425, d140819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25523 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d140192 q = 1) (hb : d140493 q = 1) : d140854 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140192, d140493, d140854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140192, d140493, d140854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25546 q ha hb
  have h3 (q : Pattern) (ha : d140193 q = 1) (hb : d140494 q = 1) : d140855 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d140193, d140494, d140855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d140193, d140494, d140855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140238 q = 1) (hb : d140562 q = 1) : d140890 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140238, d140562, d140890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140238, d140562, d140890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25569 q ha hb
  have h5 (q : Pattern) (ha : d140239 q = 1) (hb : d140563 q = 1) : d140891 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d140239, d140563, d140891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140239, d140563, d140891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d140240 q = 1) (hb : d140564 q = 1) : d140892 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d140240, d140564, d140892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140240, d140564, d140892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d140285 q = 1) (hb : d140632 q = 1) : d140927 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140285, d140632, d140927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140285, d140632, d140927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25592 q ha hb
  have h8 (q : Pattern) (ha : d140286 q = 1) (hb : d140633 q = 1) : d140928 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d140286, d140633, d140928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140286, d140633, d140928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d140287 q = 1) (hb : d140634 q = 1) : d140929 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d140287, d140634, d140929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140287, d140634, d140929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140288 q = 1) (hb : d140635 q = 1) : d140930 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d140288, d140635, d140930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d140288, d140635, d140930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d140333 q = 1) (hb : d140703 q = 1) : d140965 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d140333, d140703, d140965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140333, d140703, d140965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25615 q ha hb
  have h12 (q : Pattern) (ha : d140334 q = 1) (hb : d140704 q = 1) : d140966 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d140334, d140704, d140966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140334, d140704, d140966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140335 q = 1) (hb : d140705 q = 1) : d140967 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d140335, d140705, d140967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140335, d140705, d140967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d140336 q = 1) (hb : d140706 q = 1) : d140968 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d140336, d140706, d140968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d140336, d140706, d140968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d140337 q = 1) (hb : d140707 q = 1) : d140969 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d140337, d140707, d140969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d140337, d140707, d140969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d140338 q = 1) (hb : d140708 q = 1) : d140970 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d140338, d140708, d140970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d140338, d140708, d140970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro25617 (p : Pattern) (ha : d140344 p = 1) (hb : d140714 p = 1) : d140976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140339 q = 1) (hb : d140709 q = 1) : d140971 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d140339, d140709, d140971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25616 q ha hb
    | true =>
      simp only [d140339, d140709, d140971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140340 q = 1) (hb : d140710 q = 1) : d140972 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d140340, d140710, d140972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140340, d140710, d140972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140341 q = 1) (hb : d140711 q = 1) : d140973 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d140341, d140711, d140973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140341, d140711, d140973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140342 q = 1) (hb : d140712 q = 1) : d140974 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d140342, d140712, d140974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140342, d140712, d140974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140343 q = 1) (hb : d140713 q = 1) : d140975 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d140343, d140713, d140975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140343, d140713, d140975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140344 q = 1) (hb : d140714 q = 1) : d140976 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d140344, d140714, d140976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140344, d140714, d140976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25618 (p : Pattern) (ha : d140350 p = 1) (hb : d140720 p = 1) : d140982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140345 q = 1) (hb : d140715 q = 1) : d140977 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d140345, d140715, d140977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25617 q ha hb
    | true =>
      simp only [d140345, d140715, d140977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140346 q = 1) (hb : d140716 q = 1) : d140978 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d140346, d140716, d140978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140346, d140716, d140978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140347 q = 1) (hb : d140717 q = 1) : d140979 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d140347, d140717, d140979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140347, d140717, d140979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140348 q = 1) (hb : d140718 q = 1) : d140980 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d140348, d140718, d140980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140348, d140718, d140980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140349 q = 1) (hb : d140719 q = 1) : d140981 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d140349, d140719, d140981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140349, d140719, d140981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140350 q = 1) (hb : d140720 q = 1) : d140982 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d140350, d140720, d140982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140350, d140720, d140982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25619 (p : Pattern) (ha : d140356 p = 1) (hb : d140726 p = 1) : d140988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140351 q = 1) (hb : d140721 q = 1) : d140983 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d140351, d140721, d140983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25618 q ha hb
    | true =>
      simp only [d140351, d140721, d140983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140352 q = 1) (hb : d140722 q = 1) : d140984 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d140352, d140722, d140984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140352, d140722, d140984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140353 q = 1) (hb : d140723 q = 1) : d140985 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d140353, d140723, d140985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140353, d140723, d140985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140354 q = 1) (hb : d140724 q = 1) : d140986 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d140354, d140724, d140986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140354, d140724, d140986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140355 q = 1) (hb : d140725 q = 1) : d140987 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d140355, d140725, d140987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140355, d140725, d140987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140356 q = 1) (hb : d140726 q = 1) : d140988 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d140356, d140726, d140988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140356, d140726, d140988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25620 (p : Pattern) (ha : d140362 p = 1) (hb : d140732 p = 1) : d140994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140357 q = 1) (hb : d140727 q = 1) : d140989 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d140357, d140727, d140989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25619 q ha hb
    | true =>
      simp only [d140357, d140727, d140989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140358 q = 1) (hb : d140728 q = 1) : d140990 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d140358, d140728, d140990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140358, d140728, d140990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140359 q = 1) (hb : d140729 q = 1) : d140991 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d140359, d140729, d140991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140359, d140729, d140991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140360 q = 1) (hb : d140730 q = 1) : d140992 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d140360, d140730, d140992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140360, d140730, d140992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140361 q = 1) (hb : d140731 q = 1) : d140993 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d140361, d140731, d140993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140361, d140731, d140993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140362 q = 1) (hb : d140732 q = 1) : d140994 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d140362, d140732, d140994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140362, d140732, d140994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25621 (p : Pattern) (ha : d140368 p = 1) (hb : d140738 p = 1) : d141000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140363 q = 1) (hb : d140733 q = 1) : d140995 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d140363, d140733, d140995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25620 q ha hb
    | true =>
      simp only [d140363, d140733, d140995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140364 q = 1) (hb : d140734 q = 1) : d140996 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d140364, d140734, d140996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140364, d140734, d140996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140365 q = 1) (hb : d140735 q = 1) : d140997 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d140365, d140735, d140997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140365, d140735, d140997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140366 q = 1) (hb : d140736 q = 1) : d140998 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d140366, d140736, d140998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140366, d140736, d140998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140367 q = 1) (hb : d140737 q = 1) : d140999 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d140367, d140737, d140999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140367, d140737, d140999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140368 q = 1) (hb : d140738 q = 1) : d141000 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d140368, d140738, d141000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140368, d140738, d141000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25622 (p : Pattern) (ha : d140374 p = 1) (hb : d140744 p = 1) : d141006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140369 q = 1) (hb : d140739 q = 1) : d141001 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d140369, d140739, d141001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25621 q ha hb
    | true =>
      simp only [d140369, d140739, d141001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140370 q = 1) (hb : d140740 q = 1) : d141002 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d140370, d140740, d141002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140370, d140740, d141002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140371 q = 1) (hb : d140741 q = 1) : d141003 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d140371, d140741, d141003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140371, d140741, d141003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140372 q = 1) (hb : d140742 q = 1) : d141004 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d140372, d140742, d141004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140372, d140742, d141004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140373 q = 1) (hb : d140743 q = 1) : d141005 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d140373, d140743, d141005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140373, d140743, d141005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140374 q = 1) (hb : d140744 q = 1) : d141006 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d140374, d140744, d141006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140374, d140744, d141006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25623 (p : Pattern) (ha : d140380 p = 1) (hb : d140750 p = 1) : d141012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140375 q = 1) (hb : d140745 q = 1) : d141007 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d140375, d140745, d141007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25622 q ha hb
    | true =>
      simp only [d140375, d140745, d141007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d140376 q = 1) (hb : d140746 q = 1) : d141008 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d140376, d140746, d141008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140376, d140746, d141008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d140377 q = 1) (hb : d140747 q = 1) : d141009 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d140377, d140747, d141009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140377, d140747, d141009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d140378 q = 1) (hb : d140748 q = 1) : d141010 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d140378, d140748, d141010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140378, d140748, d141010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d140379 q = 1) (hb : d140749 q = 1) : d141011 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d140379, d140749, d141011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d140379, d140749, d141011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d140380 q = 1) (hb : d140750 q = 1) : d141012 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d140380, d140750, d141012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140380, d140750, d141012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25624 (p : Pattern) (ha : d85724 p = 1) (hb : d109112 p = 1) : d89102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10668 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25239 q ha hb
    | true =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h2 (q : Pattern) (ha : d10722 q = 1) (hb : d85724 q = 1) : d88202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10723 q = 1) (hb : d85724 q = 1) : d88203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10723, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10724 q = 1) (hb : d85724 q = 1) : d88204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10725 q = 1) (hb : d85724 q = 1) : d88205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109112 q = 1) : d89102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109112, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109112, d89102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro25625 (p : Pattern) (ha : d85724 p = 1) (hb : d109122 p = 1) : d89112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10698 q = 1) (hb : d85724 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25243 q ha hb
    | true =>
      simp only [d10698, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109118 q = 1) : d89108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109118, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109118, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109119 q = 1) : d89109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109119, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109119, d89109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109120 q = 1) : d89110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109120, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109120, d89110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109121 q = 1) : d89111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109121, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109121, d89111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109122 q = 1) : d89112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109122, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109122, d89112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25626 (p : Pattern) (ha : d85724 p = 1) (hb : d109128 p = 1) : d89118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d85724 q = 1) : d88207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25246 q ha hb
    | true =>
      simp only [d10727, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25247 q ha hb
  have h2 (q : Pattern) (ha : d10728 q = 1) (hb : d85724 q = 1) : d88208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109110 q = 1) : d89100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109110, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109110, d89100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109111 q = 1) : d89101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109111, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109111, d89101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109113 q = 1) : d89103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109113, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109113, d89103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25624 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109114 q = 1) : d89104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109114, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109114, d89104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109115 q = 1) : d89105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109115, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109115, d89105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109116 q = 1) : d89106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109116, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109116, d89106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109117 q = 1) : d89107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109117, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109117, d89107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109123 q = 1) : d89113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109123, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109123, d89113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25625 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109124 q = 1) : d89114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109124, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109124, d89114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109125 q = 1) : d89115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109125, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109125, d89115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109126 q = 1) : d89116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109126, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109126, d89116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109127 q = 1) : d89117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109127, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109127, d89117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109128 q = 1) : d89118 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109128, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109128, d89118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25627 (p : Pattern) (ha : d85724 p = 1) (hb : d109134 p = 1) : d89124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10712 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109129 q = 1) : d89119 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109129, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109129, d89119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25626 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109130 q = 1) : d89120 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109130, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109130, d89120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109131 q = 1) : d89121 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109131, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109131, d89121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109132 q = 1) : d89122 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109132, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109132, d89122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109133 q = 1) : d89123 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109133, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109133, d89123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109134 q = 1) : d89124 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109134, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d109134, d89124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25628 (p : Pattern) (ha : d85724 p = 1) (hb : d109137 p = 1) : d89127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10890 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25272 q ha hb
    | true =>
      simp only [d10890, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25273 q ha hb
  have h2 (q : Pattern) (ha : d10891 q = 1) (hb : d85724 q = 1) : d88310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10892 q = 1) (hb : d85724 q = 1) : d88311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10892, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10893 q = 1) (hb : d85724 q = 1) : d88312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10894 q = 1) (hb : d85724 q = 1) : d88313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109137 q = 1) : d89127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109137, d89127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109137, d89127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro25629 (p : Pattern) (ha : d85724 p = 1) (hb : d109148 p = 1) : d89137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109143 q = 1) : d88424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109143, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25300 q hb ha
    | true =>
      simp only [d109143, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25279 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109144 q = 1) : d89133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109144, d89133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109144, d89133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109145 q = 1) : d89134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109145, d89134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109145, d89134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109146 q = 1) : d89135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109146, d89135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109146, d89135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109147 q = 1) : d89136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109147, d89136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109147, d89136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109148 q = 1) : d89137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109148, d89137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109148, d89137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25630 (p : Pattern) (ha : d85724 p = 1) (hb : d109154 p = 1) : d89143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d85724 q = 1) : d88315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25271 q ha hb
    | true =>
      simp only [d10896, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25274 q ha hb
  have h2 (q : Pattern) (ha : d10897 q = 1) (hb : d85724 q = 1) : d88316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109135 q = 1) : d89125 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109135, d89125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109135, d89125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109136 q = 1) : d89126 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109136, d89126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109136, d89126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109138 q = 1) : d89128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109138, d89128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109138, d89128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25628 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109139 q = 1) : d89129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109139, d89129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109139, d89129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109140 q = 1) : d89130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109140, d89130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109140, d89130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109141 q = 1) : d89131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109141, d89131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109141, d89131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109142 q = 1) : d89132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109142, d89132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109142, d89132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109149 q = 1) : d89138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109149, d89138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109149, d89138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25629 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109150 q = 1) : d89139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109150, d89139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109150, d89139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109151 q = 1) : d89140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109151, d89140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109151, d89140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109152 q = 1) : d89141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109152, d89141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109152, d89141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109153 q = 1) : d89142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109153, d89142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109153, d89142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109154 q = 1) : d89143 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109154, d89143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109154, d89143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25631 (p : Pattern) (ha : d85724 p = 1) (hb : d109160 p = 1) : d89149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109155 q = 1) : d89144 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109155, d89144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109155, d89144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25630 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109156 q = 1) : d89145 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109156, d89145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109156, d89145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109157 q = 1) : d89146 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109157, d89146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109157, d89146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109158 q = 1) : d89147 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109158, d89147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109158, d89147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109159 q = 1) : d89148 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109159, d89148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109159, d89148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109160 q = 1) : d89149 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109160, d89149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109160, d89149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25632 (p : Pattern) (ha : d85724 p = 1) (hb : d109164 p = 1) : d89153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11130 q = 1) (hb : d85724 q = 1) : d88460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25310 q ha hb
    | true =>
      simp only [d11130, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25311 q ha hb
  have h2 (q : Pattern) (ha : d11131 q = 1) (hb : d85724 q = 1) : d88461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11132 q = 1) (hb : d85724 q = 1) : d88462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11132, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11133 q = 1) (hb : d85724 q = 1) : d88463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11134 q = 1) (hb : d85724 q = 1) : d88464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109164 q = 1) : d89153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109164, d89153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109164, d89153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro25633 (p : Pattern) (ha : d85724 p = 1) (hb : d109175 p = 1) : d89163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109170 q = 1) : d88575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109170, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25339 q hb ha
    | true =>
      simp only [d109170, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25317 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109171 q = 1) : d89159 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109171, d89159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109171, d89159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109172 q = 1) : d89160 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109172, d89160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109172, d89160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109173 q = 1) : d89161 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109173, d89161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109173, d89161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109174 q = 1) : d89162 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109174, d89162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109174, d89162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109175 q = 1) : d89163 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109175, d89163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109175, d89163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25634 (p : Pattern) (ha : d85724 p = 1) (hb : d109181 p = 1) : d89169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d85724 q = 1) : d88466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25309 q ha hb
    | true =>
      simp only [d11136, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25312 q ha hb
  have h2 (q : Pattern) (ha : d11137 q = 1) (hb : d85724 q = 1) : d88467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109162 q = 1) : d89151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109162, d89151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109162, d89151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109163 q = 1) : d89152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109163, d89152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109163, d89152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109165 q = 1) : d89154 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109165, d89154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109165, d89154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25632 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109166 q = 1) : d89155 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109166, d89155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109166, d89155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109167 q = 1) : d89156 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109167, d89156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109167, d89156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109168 q = 1) : d89157 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109168, d89157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109168, d89157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109169 q = 1) : d89158 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109169, d89158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109169, d89158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109176 q = 1) : d89164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109176, d89164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109176, d89164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25633 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109177 q = 1) : d89165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109177, d89165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109177, d89165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109178 q = 1) : d89166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109178, d89166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109178, d89166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109179 q = 1) : d89167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109179, d89167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109179, d89167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109180 q = 1) : d89168 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109180, d89168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109180, d89168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109181 q = 1) : d89169 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109181, d89169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109181, d89169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25635 (p : Pattern) (ha : d85724 p = 1) (hb : d109187 p = 1) : d89175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109182 q = 1) : d89170 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109182, d89170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109182, d89170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25634 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109183 q = 1) : d89171 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109183, d89171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109183, d89171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109184 q = 1) : d89172 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109184, d89172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109184, d89172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109185 q = 1) : d89173 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109185, d89173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109185, d89173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109186 q = 1) : d89174 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109186, d89174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109186, d89174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109187 q = 1) : d89175 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109187, d89175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109187, d89175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25636 (p : Pattern) (ha : d85724 p = 1) (hb : d109192 p = 1) : d89180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11400 q = 1) (hb : d85724 q = 1) : d88612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25350 q ha hb
    | true =>
      simp only [d11400, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25351 q ha hb
  have h2 (q : Pattern) (ha : d11401 q = 1) (hb : d85724 q = 1) : d88613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11402 q = 1) (hb : d85724 q = 1) : d88614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11402, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11403 q = 1) (hb : d85724 q = 1) : d88615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11404 q = 1) (hb : d85724 q = 1) : d88616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109192 q = 1) : d89180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109192, d89180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109192, d89180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro25637 (p : Pattern) (ha : d85724 p = 1) (hb : d109203 p = 1) : d89190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109198 q = 1) : d88727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109198, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25379 q hb ha
    | true =>
      simp only [d109198, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25357 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109199 q = 1) : d89186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109199, d89186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109199, d89186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109200 q = 1) : d89187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109200, d89187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109200, d89187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109201 q = 1) : d89188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109201, d89188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109201, d89188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109202 q = 1) : d89189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109202, d89189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109202, d89189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109203 q = 1) : d89190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109203, d89190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109203, d89190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25638 (p : Pattern) (ha : d85724 p = 1) (hb : d109209 p = 1) : d89196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d85724 q = 1) : d88618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25349 q ha hb
    | true =>
      simp only [d11406, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25352 q ha hb
  have h2 (q : Pattern) (ha : d11407 q = 1) (hb : d85724 q = 1) : d88619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109190 q = 1) : d89178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109190, d89178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109190, d89178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109191 q = 1) : d89179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109191, d89179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109191, d89179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109193 q = 1) : d89181 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109193, d89181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109193, d89181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25636 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109194 q = 1) : d89182 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109194, d89182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109194, d89182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109195 q = 1) : d89183 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109195, d89183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109195, d89183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109196 q = 1) : d89184 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109196, d89184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109196, d89184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109197 q = 1) : d89185 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109197, d89185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109197, d89185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109204 q = 1) : d89191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109204, d89191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109204, d89191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25637 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109205 q = 1) : d89192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109205, d89192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109205, d89192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109206 q = 1) : d89193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109206, d89193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109206, d89193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109207 q = 1) : d89194 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109207, d89194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109207, d89194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109208 q = 1) : d89195 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109208, d89195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109208, d89195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109209 q = 1) : d89196 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109209, d89196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109209, d89196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25639 (p : Pattern) (ha : d85724 p = 1) (hb : d109215 p = 1) : d89202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109210 q = 1) : d89197 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109210, d89197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109210, d89197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25638 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109211 q = 1) : d89198 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109211, d89198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109211, d89198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109212 q = 1) : d89199 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109212, d89199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109212, d89199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109213 q = 1) : d89200 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109213, d89200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109213, d89200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109214 q = 1) : d89201 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109214, d89201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109214, d89201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109215 q = 1) : d89202 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109215, d89202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109215, d89202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25640 (p : Pattern) (ha : d85724 p = 1) (hb : d109221 p = 1) : d89208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11671 q = 1) (hb : d85724 q = 1) : d88765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25390 q ha hb
    | true =>
      simp only [d11671, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25391 q ha hb
  have h2 (q : Pattern) (ha : d11672 q = 1) (hb : d85724 q = 1) : d88766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11673 q = 1) (hb : d85724 q = 1) : d88767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11673, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11674 q = 1) (hb : d85724 q = 1) : d88768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11675 q = 1) (hb : d85724 q = 1) : d88769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109221 q = 1) : d89208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109221, d89208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109221, d89208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro25641 (p : Pattern) (ha : d85724 p = 1) (hb : d109232 p = 1) : d89218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109227 q = 1) : d88880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109227, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25419 q hb ha
    | true =>
      simp only [d109227, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25397 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109228 q = 1) : d89214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109228, d89214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109228, d89214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109229 q = 1) : d89215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109229, d89215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109229, d89215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109230 q = 1) : d89216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109230, d89216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109230, d89216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109231 q = 1) : d89217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109231, d89217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109231, d89217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109232 q = 1) : d89218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109232, d89218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109232, d89218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25642 (p : Pattern) (ha : d85724 p = 1) (hb : d109238 p = 1) : d89224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d85724 q = 1) : d88771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25389 q ha hb
    | true =>
      simp only [d11677, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25392 q ha hb
  have h2 (q : Pattern) (ha : d11678 q = 1) (hb : d85724 q = 1) : d88772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109219 q = 1) : d89206 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109219, d89206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109219, d89206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109220 q = 1) : d89207 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109220, d89207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109220, d89207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109222 q = 1) : d89209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109222, d89209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109222, d89209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25640 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109223 q = 1) : d89210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109223, d89210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109223, d89210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109224 q = 1) : d89211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109224, d89211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109224, d89211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109225 q = 1) : d89212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109225, d89212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109225, d89212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109226 q = 1) : d89213 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109226, d89213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109226, d89213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109233 q = 1) : d89219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109233, d89219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109233, d89219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25641 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109234 q = 1) : d89220 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109234, d89220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109234, d89220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109235 q = 1) : d89221 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109235, d89221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109235, d89221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109236 q = 1) : d89222 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109236, d89222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109236, d89222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109237 q = 1) : d89223 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109237, d89223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109237, d89223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109238 q = 1) : d89224 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109238, d89224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109238, d89224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25643 (p : Pattern) (ha : d85724 p = 1) (hb : d109244 p = 1) : d89230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109239 q = 1) : d89225 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109239, d89225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109239, d89225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25642 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109240 q = 1) : d89226 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109240, d89226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109240, d89226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109241 q = 1) : d89227 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109241, d89227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109241, d89227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109242 q = 1) : d89228 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109242, d89228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109242, d89228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109243 q = 1) : d89229 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109243, d89229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109243, d89229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109244 q = 1) : d89230 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109244, d89230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109244, d89230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25644 (p : Pattern) (ha : d85724 p = 1) (hb : d109251 p = 1) : d89237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11943 q = 1) (hb : d85724 q = 1) : d88919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25430 q ha hb
    | true =>
      simp only [d11943, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25431 q ha hb
  have h2 (q : Pattern) (ha : d11944 q = 1) (hb : d85724 q = 1) : d88920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11945 q = 1) (hb : d85724 q = 1) : d88921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11945, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11946 q = 1) (hb : d85724 q = 1) : d88922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11947 q = 1) (hb : d85724 q = 1) : d88923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109251 q = 1) : d89237 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109251, d89237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109251, d89237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro25645 (p : Pattern) (ha : d85724 p = 1) (hb : d109262 p = 1) : d89247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109257 q = 1) : d89034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109257, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25459 q hb ha
    | true =>
      simp only [d109257, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25437 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109258 q = 1) : d89243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109258, d89243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109258, d89243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109259 q = 1) : d89244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109259, d89244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109259, d89244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109260 q = 1) : d89245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109260, d89245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109260, d89245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109261 q = 1) : d89246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109261, d89246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109261, d89246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109262 q = 1) : d89247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109262, d89247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109262, d89247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25646 (p : Pattern) (ha : d85724 p = 1) (hb : d109268 p = 1) : d89253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d85724 q = 1) : d88925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25429 q ha hb
    | true =>
      simp only [d11949, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25432 q ha hb
  have h2 (q : Pattern) (ha : d11950 q = 1) (hb : d85724 q = 1) : d88926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109249 q = 1) : d89235 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109249, d89235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109249, d89235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109250 q = 1) : d89236 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109250, d89236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109250, d89236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109252 q = 1) : d89238 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109252, d89238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109252, d89238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25644 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109253 q = 1) : d89239 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109253, d89239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109253, d89239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109254 q = 1) : d89240 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109254, d89240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109254, d89240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109255 q = 1) : d89241 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109255, d89241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109255, d89241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109256 q = 1) : d89242 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109256, d89242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109256, d89242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109263 q = 1) : d89248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109263, d89248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109263, d89248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25645 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109264 q = 1) : d89249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109264, d89249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109264, d89249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109265 q = 1) : d89250 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109265, d89250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109265, d89250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109266 q = 1) : d89251 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109266, d89251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109266, d89251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109267 q = 1) : d89252 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109267, d89252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109267, d89252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109268 q = 1) : d89253 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109268, d89253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109268, d89253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25647 (p : Pattern) (ha : d85724 p = 1) (hb : d109274 p = 1) : d89259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109269 q = 1) : d89254 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109269, d89254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109269, d89254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25646 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109270 q = 1) : d89255 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109270, d89255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109270, d89255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109271 q = 1) : d89256 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109271, d89256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109271, d89256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109272 q = 1) : d89257 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109272, d89257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109272, d89257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109273 q = 1) : d89258 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109273, d89258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109273, d89258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109274 q = 1) : d89259 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109274, d89259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109274, d89259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25648 (p : Pattern) (ha : d85724 p = 1) (hb : d109280 p = 1) : d89265 p = 1 := by
  have h0 (q : Pattern) (ha : d85724 q = 1) (hb : d109161 q = 1) : d89150 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109161, d89150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25627 q ha hb
    | true =>
      simp only [d109161, d89150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25631 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109188 q = 1) : d89176 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109188, d89176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109188, d89176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25635 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109189 q = 1) : d89177 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109189, d89177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109189, d89177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109216 q = 1) : d89203 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109216, d89203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109216, d89203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25639 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109217 q = 1) : d89204 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109217, d89204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109217, d89204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109218 q = 1) : d89205 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109218, d89205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109218, d89205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109245 q = 1) : d89231 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109245, d89231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109245, d89231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25643 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109246 q = 1) : d89232 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109246, d89232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109246, d89232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109247 q = 1) : d89233 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109247, d89233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109247, d89233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109248 q = 1) : d89234 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109248, d89234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109248, d89234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109275 q = 1) : d89260 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109275, d89260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109275, d89260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25647 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109276 q = 1) : d89261 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109276, d89261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109276, d89261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109277 q = 1) : d89262 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109277, d89262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109277, d89262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109278 q = 1) : d89263 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109278, d89263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109278, d89263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109279 q = 1) : d89264 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109279, d89264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109279, d89264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d109280 q = 1) : d89265 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109280, d89265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109280, d89265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro25649 (p : Pattern) (ha : d85724 p = 1) (hb : d109286 p = 1) : d89271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109281 q = 1) : d89266 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109281, d89266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25648 q ha hb
    | true =>
      simp only [d109281, d89266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109282 q = 1) : d89267 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109282, d89267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109282, d89267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109283 q = 1) : d89268 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109283, d89268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109283, d89268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109284 q = 1) : d89269 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109284, d89269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109284, d89269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109285 q = 1) : d89270 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109285, d89270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109285, d89270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109286 q = 1) : d89271 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109286, d89271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109286, d89271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25650 (p : Pattern) (ha : d85724 p = 1) (hb : d109292 p = 1) : d89277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109287 q = 1) : d89272 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109287, d89272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25649 q ha hb
    | true =>
      simp only [d109287, d89272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109288 q = 1) : d89273 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109288, d89273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109288, d89273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109289 q = 1) : d89274 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109289, d89274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109289, d89274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109290 q = 1) : d89275 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109290, d89275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109290, d89275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109291 q = 1) : d89276 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109291, d89276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109291, d89276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109292 q = 1) : d89277 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109292, d89277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109292, d89277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25651 (p : Pattern) (ha : d85724 p = 1) (hb : d109298 p = 1) : d89283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109293 q = 1) : d89278 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109293, d89278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25650 q ha hb
    | true =>
      simp only [d109293, d89278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109294 q = 1) : d89279 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109294, d89279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109294, d89279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109295 q = 1) : d89280 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109295, d89280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109295, d89280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109296 q = 1) : d89281 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109296, d89281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109296, d89281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109297 q = 1) : d89282 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109297, d89282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109297, d89282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109298 q = 1) : d89283 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109298, d89283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109298, d89283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25652 (p : Pattern) (ha : d85724 p = 1) (hb : d109304 p = 1) : d89289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109299 q = 1) : d89284 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109299, d89284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25651 q ha hb
    | true =>
      simp only [d109299, d89284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109300 q = 1) : d89285 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109300, d89285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109300, d89285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109301 q = 1) : d89286 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109301, d89286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109301, d89286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109302 q = 1) : d89287 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109302, d89287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109302, d89287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109303 q = 1) : d89288 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109303, d89288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109303, d89288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109304 q = 1) : d89289 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109304, d89289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109304, d89289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25653 (p : Pattern) (ha : d85724 p = 1) (hb : d109310 p = 1) : d89295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109305 q = 1) : d89290 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109305, d89290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25652 q ha hb
    | true =>
      simp only [d109305, d89290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109306 q = 1) : d89291 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109306, d89291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109306, d89291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109307 q = 1) : d89292 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109307, d89292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109307, d89292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109308 q = 1) : d89293 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109308, d89293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109308, d89293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109309 q = 1) : d89294 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109309, d89294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109309, d89294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109310 q = 1) : d89295 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109310, d89295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109310, d89295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25654 (p : Pattern) (ha : d85724 p = 1) (hb : d109316 p = 1) : d89301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109311 q = 1) : d89296 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109311, d89296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25653 q ha hb
    | true =>
      simp only [d109311, d89296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109312 q = 1) : d89297 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109312, d89297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109312, d89297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109313 q = 1) : d89298 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109313, d89298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109313, d89298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109314 q = 1) : d89299 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109314, d89299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109314, d89299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109315 q = 1) : d89300 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109315, d89300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109315, d89300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109316 q = 1) : d89301 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109316, d89301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109316, d89301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25655 (p : Pattern) (ha : d85724 p = 1) (hb : d109322 p = 1) : d89307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109317 q = 1) : d89302 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109317, d89302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25654 q ha hb
    | true =>
      simp only [d109317, d89302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109318 q = 1) : d89303 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109318, d89303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109318, d89303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109319 q = 1) : d89304 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109319, d89304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109319, d89304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109320 q = 1) : d89305 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109320, d89305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109320, d89305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109321 q = 1) : d89306 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109321, d89306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109321, d89306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109322 q = 1) : d89307 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109322, d89307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109322, d89307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25656 (p : Pattern) (ha : d88199 p = 1) (hb : d140070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78867 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78881 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d78881, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88196 q = 1) (hb : d140067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d140067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d88196, d140067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88197 q = 1) (hb : d140068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d140068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88197, d140068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88198 q = 1) (hb : d140069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d140069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88198, d140069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88199 q = 1) (hb : d140070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88199, d140070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88199, d140070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25657 (p : Pattern) (ha : d88206 p = 1) (hb : d140074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78867 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78881 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d78881, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88196 q = 1) (hb : d140067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d140067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d88196, d140067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d88197 q = 1) (hb : d140068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d140068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88197, d140068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88198 q = 1) (hb : d140069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d140069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88198, d140069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78890 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78894 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d78896 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d78808 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
    | true =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d78897 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d78897, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88203 q = 1) (hb : d140071 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d140071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d88203, d140071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d88204 q = 1) (hb : d140072 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d140072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88204, d140072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88205 q = 1) (hb : d140073 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d140073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88205, d140073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88206 q = 1) (hb : d140074 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88206, d140074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88206, d140074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25658 (p : Pattern) (ha : d89102 p = 1) (hb : d140081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78896 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78808 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
    | true =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78897 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78897, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88203 q = 1) (hb : d140071 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d140071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d88203, d140071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88204 q = 1) (hb : d140079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d140079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88204, d140079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88205 q = 1) (hb : d140080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d140080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88205, d140080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89102 q = 1) (hb : d140081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89102, d140081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89102, d140081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25659 (p : Pattern) (ha : d89112 p = 1) (hb : d140090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78830 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78830, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25480 q ha hb
    | true =>
      simp only [d78830, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78923 q = 1) (hb : d89108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78923, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d78923, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89109 q = 1) (hb : d140087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89109, d140087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d89109, d140087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89110 q = 1) (hb : d140088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89110, d140088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89110, d140088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89111 q = 1) (hb : d140089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89111, d140089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89111, d140089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89112 q = 1) (hb : d140090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89112, d140090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89112, d140090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25660 (p : Pattern) (ha : d89118 p = 1) (hb : d140096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88207 q = 1) (hb : d140075 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88207, d140075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25656 q ha hb
    | true =>
      simp only [d88207, d140075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25657 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78904 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88208 q = 1) (hb : d140076 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88208, d140076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88208, d140076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89100 q = 1) (hb : d140077 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89100, d140077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89100, d140077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89101 q = 1) (hb : d140078 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89101, d140078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89101, d140078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89103 q = 1) (hb : d140082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89103, d140082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89103, d140082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25658 q ha hb
  have h8 (q : Pattern) (ha : d89104 q = 1) (hb : d140083 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89104, d140083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89104, d140083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89105 q = 1) (hb : d140084 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89105, d140084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89105, d140084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89106 q = 1) (hb : d140085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89106, d140085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89106, d140085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89107 q = 1) (hb : d140086 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89107, d140086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89107, d140086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89113 q = 1) (hb : d140091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89113, d140091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89113, d140091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25659 q ha hb
  have h13 (q : Pattern) (ha : d89114 q = 1) (hb : d140092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89114, d140092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89114, d140092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89115 q = 1) (hb : d140093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89115, d140093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89115, d140093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89116 q = 1) (hb : d140094 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89116, d140094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89116, d140094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89117 q = 1) (hb : d140095 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89117, d140095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89117, d140095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89118 q = 1) (hb : d140096 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89118, d140096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89118, d140096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25661 (p : Pattern) (ha : d89124 p = 1) (hb : d140102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78846 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89119 q = 1) (hb : d140097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89119, d140097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89119, d140097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25660 q ha hb
  have h3 (q : Pattern) (ha : d89120 q = 1) (hb : d140098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89120, d140098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89120, d140098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89121 q = 1) (hb : d140099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89121, d140099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89121, d140099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89122 q = 1) (hb : d140100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89122, d140100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89122, d140100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89123 q = 1) (hb : d140101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89123, d140101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89123, d140101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89124 q = 1) (hb : d140102 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89124, d140102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89124, d140102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25662 (p : Pattern) (ha : d88305 p = 1) (hb : d140108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78969 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d140103 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78946 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
    | true =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88301 q = 1) (hb : d140104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88301, d140104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88301, d140104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88302 q = 1) (hb : d140105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88302, d140105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88302, d140105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88303 q = 1) (hb : d140106 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88303, d140106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88303, d140106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88304 q = 1) (hb : d140107 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88304, d140107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88304, d140107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88305 q = 1) (hb : d140108 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88305, d140108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88305, d140108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25663 (p : Pattern) (ha : d88314 p = 1) (hb : d140114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140103 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78946 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25502 q ha hb
    | true =>
      simp only [d78946, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88301 q = 1) (hb : d140104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88301, d140104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88301, d140104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88302 q = 1) (hb : d140105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88302, d140105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88302, d140105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d88303 q = 1) (hb : d140106 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88303, d140106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88303, d140106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88304 q = 1) (hb : d140107 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88304, d140107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88304, d140107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78999 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79003 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d140109 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d78955 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25504 q ha hb
    | true =>
      simp only [d78955, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d88310 q = 1) (hb : d140110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88310, d140110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88310, d140110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88311 q = 1) (hb : d140111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88311, d140111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88311, d140111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d88312 q = 1) (hb : d140112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88312, d140112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88312, d140112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88313 q = 1) (hb : d140113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88313, d140113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88313, d140113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88314 q = 1) (hb : d140114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88314, d140114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88314, d140114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25664 (p : Pattern) (ha : d89127 p = 1) (hb : d140123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78955 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78955, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25504 q ha hb
    | true =>
      simp only [d78955, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88310 q = 1) (hb : d140110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88310, d140110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88310, d140110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88311 q = 1) (hb : d140111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88311, d140111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88311, d140111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88312 q = 1) (hb : d140121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88312, d140121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88312, d140121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88313 q = 1) (hb : d140122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88313, d140122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88313, d140122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89127 q = 1) (hb : d140123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89127, d140123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89127, d140123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25665 (p : Pattern) (ha : d89137 p = 1) (hb : d140134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79051 q = 1) (hb : d88424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79051, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25520 q ha hb
    | true =>
      simp only [d79051, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d89133 q = 1) (hb : d140130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89133, d140130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89133, d140130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89134 q = 1) (hb : d140131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89134, d140131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89134, d140131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89135 q = 1) (hb : d140132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89135, d140132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89135, d140132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89136 q = 1) (hb : d140133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89136, d140133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89136, d140133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89137 q = 1) (hb : d140134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89137, d140134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89137, d140134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25666 (p : Pattern) (ha : d89143 p = 1) (hb : d140140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78963 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88315 q = 1) (hb : d140115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88315, d140115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25662 q ha hb
    | true =>
      simp only [d88315, d140115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25663 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88316 q = 1) (hb : d140118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88316, d140118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88316, d140118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89125 q = 1) (hb : d140119 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89125, d140119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89125, d140119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89126 q = 1) (hb : d140120 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89126, d140120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89126, d140120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89128 q = 1) (hb : d140124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89128, d140124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89128, d140124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25664 q ha hb
  have h8 (q : Pattern) (ha : d89129 q = 1) (hb : d140125 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89129, d140125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89129, d140125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89130 q = 1) (hb : d140126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89130, d140126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89130, d140126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89131 q = 1) (hb : d140127 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89131, d140127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89131, d140127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89132 q = 1) (hb : d140128 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89132, d140128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89132, d140128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89138 q = 1) (hb : d140135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89138, d140135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89138, d140135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25665 q ha hb
  have h13 (q : Pattern) (ha : d89139 q = 1) (hb : d140136 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89139, d140136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89139, d140136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89140 q = 1) (hb : d140137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89140, d140137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89140, d140137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89141 q = 1) (hb : d140138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89141, d140138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89141, d140138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89142 q = 1) (hb : d140139 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89142, d140139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89142, d140139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89143 q = 1) (hb : d140140 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89143, d140140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89143, d140140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25667 (p : Pattern) (ha : d89149 p = 1) (hb : d140146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89144 q = 1) (hb : d140141 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89144, d140141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89144, d140141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25666 q ha hb
  have h2 (q : Pattern) (ha : d89145 q = 1) (hb : d140142 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89145, d140142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89145, d140142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89146 q = 1) (hb : d140143 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89146, d140143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89146, d140143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89147 q = 1) (hb : d140144 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89147, d140144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89147, d140144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89148 q = 1) (hb : d140145 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89148, d140145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89148, d140145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89149 q = 1) (hb : d140146 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89149, d140146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89149, d140146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25668 (p : Pattern) (ha : d88456 p = 1) (hb : d140153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d140148 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79077 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
    | true =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88452 q = 1) (hb : d140149 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88452, d140149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88452, d140149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88453 q = 1) (hb : d140150 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88453, d140150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88453, d140150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88454 q = 1) (hb : d140151 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88454, d140151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88454, d140151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88455 q = 1) (hb : d140152 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88455, d140152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88455, d140152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88456 q = 1) (hb : d140153 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88456, d140153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88456, d140153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25669 (p : Pattern) (ha : d88465 p = 1) (hb : d140159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140148 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79077 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25525 q ha hb
    | true =>
      simp only [d79077, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88452 q = 1) (hb : d140149 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88452, d140149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88452, d140149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88453 q = 1) (hb : d140150 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88453, d140150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88453, d140150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d88454 q = 1) (hb : d140151 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88454, d140151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88454, d140151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88455 q = 1) (hb : d140152 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88455, d140152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88455, d140152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79130 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79134 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d140154 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d79086 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25527 q ha hb
    | true =>
      simp only [d79086, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d88461 q = 1) (hb : d140155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88461, d140155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88461, d140155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88462 q = 1) (hb : d140156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88462, d140156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88462, d140156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d88463 q = 1) (hb : d140157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88463, d140157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88463, d140157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88464 q = 1) (hb : d140158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88464, d140158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88464, d140158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88465 q = 1) (hb : d140159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88465, d140159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88465, d140159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25670 (p : Pattern) (ha : d89153 p = 1) (hb : d140168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79086 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79086, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25527 q ha hb
    | true =>
      simp only [d79086, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88461 q = 1) (hb : d140155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88461, d140155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88461, d140155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88462 q = 1) (hb : d140156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88462, d140156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88462, d140156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88463 q = 1) (hb : d140166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88463, d140166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88463, d140166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88464 q = 1) (hb : d140167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88464, d140167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88464, d140167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89153 q = 1) (hb : d140168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89153, d140168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89153, d140168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25671 (p : Pattern) (ha : d89163 p = 1) (hb : d140179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79182 q = 1) (hb : d88575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79182, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25543 q ha hb
    | true =>
      simp only [d79182, d88575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d89159 q = 1) (hb : d140175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89159, d140175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89159, d140175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89160 q = 1) (hb : d140176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89160, d140176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89160, d140176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89161 q = 1) (hb : d140177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89161, d140177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89161, d140177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89162 q = 1) (hb : d140178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89162, d140178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89162, d140178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89163 q = 1) (hb : d140179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89163, d140179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89163, d140179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25672 (p : Pattern) (ha : d89169 p = 1) (hb : d140185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79094 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88466 q = 1) (hb : d140160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88466, d140160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25668 q ha hb
    | true =>
      simp only [d88466, d140160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25669 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88467 q = 1) (hb : d140163 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88467, d140163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88467, d140163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89151 q = 1) (hb : d140164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89151, d140164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89151, d140164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89152 q = 1) (hb : d140165 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89152, d140165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89152, d140165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89154 q = 1) (hb : d140169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89154, d140169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89154, d140169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25670 q ha hb
  have h8 (q : Pattern) (ha : d89155 q = 1) (hb : d140170 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89155, d140170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89155, d140170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89156 q = 1) (hb : d140171 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89156, d140171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89156, d140171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89157 q = 1) (hb : d140172 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89157, d140172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89157, d140172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89158 q = 1) (hb : d140173 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89158, d140173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89158, d140173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89164 q = 1) (hb : d140180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89164, d140180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89164, d140180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25671 q ha hb
  have h13 (q : Pattern) (ha : d89165 q = 1) (hb : d140181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89165, d140181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89165, d140181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89166 q = 1) (hb : d140182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89166, d140182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89166, d140182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89167 q = 1) (hb : d140183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89167, d140183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89167, d140183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89168 q = 1) (hb : d140184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89168, d140184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89168, d140184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89169 q = 1) (hb : d140185 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89169, d140185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89169, d140185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25673 (p : Pattern) (ha : d89175 p = 1) (hb : d140191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89170 q = 1) (hb : d140186 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89170, d140186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89170, d140186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25672 q ha hb
  have h2 (q : Pattern) (ha : d89171 q = 1) (hb : d140187 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89171, d140187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89171, d140187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89172 q = 1) (hb : d140188 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89172, d140188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89172, d140188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89173 q = 1) (hb : d140189 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89173, d140189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89173, d140189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89174 q = 1) (hb : d140190 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89174, d140190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89174, d140190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89175 q = 1) (hb : d140191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89175, d140191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89175, d140191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25674 (p : Pattern) (ha : d88608 p = 1) (hb : d140199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79232 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d140194 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79209 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
    | true =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88604 q = 1) (hb : d140195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88604, d140195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88604, d140195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88605 q = 1) (hb : d140196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88605, d140196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88605, d140196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88606 q = 1) (hb : d140197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88606, d140197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88606, d140197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88607 q = 1) (hb : d140198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88607, d140198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88607, d140198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88608 q = 1) (hb : d140199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88608, d140199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88608, d140199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25675 (p : Pattern) (ha : d88617 p = 1) (hb : d140205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79232 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140194 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79209 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25548 q ha hb
    | true =>
      simp only [d79209, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88604 q = 1) (hb : d140195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88604, d140195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88604, d140195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88605 q = 1) (hb : d140196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88605, d140196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88605, d140196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d88606 q = 1) (hb : d140197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88606, d140197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88606, d140197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88607 q = 1) (hb : d140198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88607, d140198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88607, d140198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79262 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79266 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d140200 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d79218 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25550 q ha hb
    | true =>
      simp only [d79218, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d88613 q = 1) (hb : d140201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88613, d140201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88613, d140201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88614 q = 1) (hb : d140202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88614, d140202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88614, d140202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d88615 q = 1) (hb : d140203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88615, d140203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88615, d140203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88616 q = 1) (hb : d140204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88616, d140204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88616, d140204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88617 q = 1) (hb : d140205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88617, d140205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88617, d140205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25676 (p : Pattern) (ha : d89180 p = 1) (hb : d140214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140200 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79218 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79218, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25550 q ha hb
    | true =>
      simp only [d79218, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88613 q = 1) (hb : d140201 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88613, d140201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88613, d140201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88614 q = 1) (hb : d140202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88614, d140202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88614, d140202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88615 q = 1) (hb : d140212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88615, d140212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88615, d140212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88616 q = 1) (hb : d140213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88616, d140213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88616, d140213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89180 q = 1) (hb : d140214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89180, d140214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89180, d140214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25677 (p : Pattern) (ha : d89190 p = 1) (hb : d140225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140220 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79314 q = 1) (hb : d88727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79314, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25566 q ha hb
    | true =>
      simp only [d79314, d88727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d89186 q = 1) (hb : d140221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89186, d140221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89186, d140221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89187 q = 1) (hb : d140222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89187, d140222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89187, d140222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89188 q = 1) (hb : d140223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89188, d140223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89188, d140223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89189 q = 1) (hb : d140224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89189, d140224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89189, d140224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89190 q = 1) (hb : d140225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89190, d140225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89190, d140225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25678 (p : Pattern) (ha : d89196 p = 1) (hb : d140231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79226 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88618 q = 1) (hb : d140206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88618, d140206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25674 q ha hb
    | true =>
      simp only [d88618, d140206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25675 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88619 q = 1) (hb : d140209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88619, d140209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88619, d140209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89178 q = 1) (hb : d140210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89178, d140210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89178, d140210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89179 q = 1) (hb : d140211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89179, d140211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89179, d140211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89181 q = 1) (hb : d140215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89181, d140215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89181, d140215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25676 q ha hb
  have h8 (q : Pattern) (ha : d89182 q = 1) (hb : d140216 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89182, d140216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89182, d140216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89183 q = 1) (hb : d140217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89183, d140217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89183, d140217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89184 q = 1) (hb : d140218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89184, d140218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89184, d140218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89185 q = 1) (hb : d140219 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89185, d140219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89185, d140219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89191 q = 1) (hb : d140226 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89191, d140226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89191, d140226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25677 q ha hb
  have h13 (q : Pattern) (ha : d89192 q = 1) (hb : d140227 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89192, d140227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89192, d140227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89193 q = 1) (hb : d140228 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89193, d140228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89193, d140228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89194 q = 1) (hb : d140229 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89194, d140229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89194, d140229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89195 q = 1) (hb : d140230 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89195, d140230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89195, d140230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89196 q = 1) (hb : d140231 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89196, d140231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89196, d140231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25679 (p : Pattern) (ha : d89202 p = 1) (hb : d140237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89197 q = 1) (hb : d140232 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89197, d140232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89197, d140232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25678 q ha hb
  have h2 (q : Pattern) (ha : d89198 q = 1) (hb : d140233 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89198, d140233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89198, d140233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89199 q = 1) (hb : d140234 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89199, d140234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89199, d140234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89200 q = 1) (hb : d140235 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89200, d140235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89200, d140235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89201 q = 1) (hb : d140236 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89201, d140236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89201, d140236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89202 q = 1) (hb : d140237 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89202, d140237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89202, d140237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25680 (p : Pattern) (ha : d88761 p = 1) (hb : d140246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79365 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d140241 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79342 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
    | true =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88757 q = 1) (hb : d140242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88757, d140242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88757, d140242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88758 q = 1) (hb : d140243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88758, d140243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88758, d140243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88759 q = 1) (hb : d140244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88759, d140244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88759, d140244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88760 q = 1) (hb : d140245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88760, d140245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88760, d140245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88761 q = 1) (hb : d140246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88761, d140246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88761, d140246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25681 (p : Pattern) (ha : d88770 p = 1) (hb : d140252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79365 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79371 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140241 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79342 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25571 q ha hb
    | true =>
      simp only [d79342, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88757 q = 1) (hb : d140242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88757, d140242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88757, d140242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88758 q = 1) (hb : d140243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88758, d140243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88758, d140243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d88759 q = 1) (hb : d140244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88759, d140244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88759, d140244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88760 q = 1) (hb : d140245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88760, d140245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88760, d140245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79395 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79399 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d140247 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d79351 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25573 q ha hb
    | true =>
      simp only [d79351, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d88766 q = 1) (hb : d140248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88766, d140248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88766, d140248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88767 q = 1) (hb : d140249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88767, d140249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88767, d140249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d88768 q = 1) (hb : d140250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88768, d140250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88768, d140250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88769 q = 1) (hb : d140251 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88769, d140251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88769, d140251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88770 q = 1) (hb : d140252 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88770, d140252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88770, d140252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25682 (p : Pattern) (ha : d89208 p = 1) (hb : d140261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79351 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79351, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25573 q ha hb
    | true =>
      simp only [d79351, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88766 q = 1) (hb : d140248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88766, d140248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88766, d140248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88767 q = 1) (hb : d140249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88767, d140249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88767, d140249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88768 q = 1) (hb : d140259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88768, d140259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88768, d140259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88769 q = 1) (hb : d140260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88769, d140260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88769, d140260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89208 q = 1) (hb : d140261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89208, d140261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89208, d140261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25683 (p : Pattern) (ha : d89218 p = 1) (hb : d140272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79447 q = 1) (hb : d88880 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79447, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25589 q ha hb
    | true =>
      simp only [d79447, d88880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d89214 q = 1) (hb : d140268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89214, d140268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89214, d140268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89215 q = 1) (hb : d140269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89215, d140269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89215, d140269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89216 q = 1) (hb : d140270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89216, d140270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89216, d140270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89217 q = 1) (hb : d140271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89217, d140271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89217, d140271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89218 q = 1) (hb : d140272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89218, d140272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89218, d140272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25684 (p : Pattern) (ha : d89224 p = 1) (hb : d140278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88771 q = 1) (hb : d140253 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88771, d140253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25680 q ha hb
    | true =>
      simp only [d88771, d140253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25681 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88772 q = 1) (hb : d140256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88772, d140256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88772, d140256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89206 q = 1) (hb : d140257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89206, d140257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89206, d140257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89207 q = 1) (hb : d140258 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89207, d140258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89207, d140258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89209 q = 1) (hb : d140262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89209, d140262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89209, d140262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25682 q ha hb
  have h8 (q : Pattern) (ha : d89210 q = 1) (hb : d140263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89210, d140263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89210, d140263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89211 q = 1) (hb : d140264 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89211, d140264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89211, d140264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89212 q = 1) (hb : d140265 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89212, d140265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89212, d140265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89213 q = 1) (hb : d140266 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89213, d140266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89213, d140266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89219 q = 1) (hb : d140273 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89219, d140273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89219, d140273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25683 q ha hb
  have h13 (q : Pattern) (ha : d89220 q = 1) (hb : d140274 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89220, d140274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89220, d140274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89221 q = 1) (hb : d140275 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89221, d140275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89221, d140275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89222 q = 1) (hb : d140276 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89222, d140276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89222, d140276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89223 q = 1) (hb : d140277 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89223, d140277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89223, d140277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89224 q = 1) (hb : d140278 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89224, d140278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89224, d140278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25685 (p : Pattern) (ha : d89230 p = 1) (hb : d140284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89225 q = 1) (hb : d140279 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89225, d140279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89225, d140279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25684 q ha hb
  have h2 (q : Pattern) (ha : d89226 q = 1) (hb : d140280 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89226, d140280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89226, d140280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89227 q = 1) (hb : d140281 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89227, d140281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89227, d140281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89228 q = 1) (hb : d140282 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89228, d140282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89228, d140282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89229 q = 1) (hb : d140283 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89229, d140283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89229, d140283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89230 q = 1) (hb : d140284 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89230, d140284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89230, d140284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25686 (p : Pattern) (ha : d88915 p = 1) (hb : d140294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d79505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d140289 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79476 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
    | true =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d88911 q = 1) (hb : d140290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88911, d140290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88911, d140290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88912 q = 1) (hb : d140291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88912, d140291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88912, d140291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88913 q = 1) (hb : d140292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88913, d140292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88913, d140292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88914 q = 1) (hb : d140293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88914, d140293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88914, d140293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88915 q = 1) (hb : d140294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88915, d140294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88915, d140294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25687 (p : Pattern) (ha : d88924 p = 1) (hb : d140300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79476 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25594 q ha hb
    | true =>
      simp only [d79476, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d88911 q = 1) (hb : d140290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88911, d140290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88911, d140290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88912 q = 1) (hb : d140291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88912, d140291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88912, d140291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d88913 q = 1) (hb : d140292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88913, d140292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88913, d140292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88914 q = 1) (hb : d140293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88914, d140293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88914, d140293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d79529 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d79533 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d140295 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d79485 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25596 q ha hb
    | true =>
      simp only [d79485, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d88920 q = 1) (hb : d140296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88920, d140296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88920, d140296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88921 q = 1) (hb : d140297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88921, d140297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88921, d140297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d88922 q = 1) (hb : d140298 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88922, d140298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88922, d140298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88923 q = 1) (hb : d140299 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88923, d140299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88923, d140299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88924 q = 1) (hb : d140300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88924, d140300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88924, d140300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25688 (p : Pattern) (ha : d89237 p = 1) (hb : d140309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79485 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79485, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25596 q ha hb
    | true =>
      simp only [d79485, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d88920 q = 1) (hb : d140296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88920, d140296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88920, d140296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88921 q = 1) (hb : d140297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88921, d140297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88921, d140297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88922 q = 1) (hb : d140307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88922, d140307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88922, d140307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88923 q = 1) (hb : d140308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88923, d140308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88923, d140308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89237 q = 1) (hb : d140309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89237, d140309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89237, d140309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25689 (p : Pattern) (ha : d89247 p = 1) (hb : d140320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79581 q = 1) (hb : d89034 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79581, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25612 q ha hb
    | true =>
      simp only [d79581, d89034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d89243 q = 1) (hb : d140316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89243, d140316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89243, d140316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89244 q = 1) (hb : d140317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89244, d140317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89244, d140317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89245 q = 1) (hb : d140318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89245, d140318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89245, d140318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89246 q = 1) (hb : d140319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89246, d140319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89246, d140319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89247 q = 1) (hb : d140320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89247, d140320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89247, d140320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25690 (p : Pattern) (ha : d89253 p = 1) (hb : d140326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d79493 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88925 q = 1) (hb : d140301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88925, d140301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25686 q ha hb
    | true =>
      simp only [d88925, d140301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25687 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d140303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88926 q = 1) (hb : d140304 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88926, d140304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88926, d140304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89235 q = 1) (hb : d140305 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89235, d140305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89235, d140305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89236 q = 1) (hb : d140306 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89236, d140306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89236, d140306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89238 q = 1) (hb : d140310 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89238, d140310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89238, d140310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25688 q ha hb
  have h8 (q : Pattern) (ha : d89239 q = 1) (hb : d140311 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89239, d140311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89239, d140311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89240 q = 1) (hb : d140312 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89240, d140312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89240, d140312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89241 q = 1) (hb : d140313 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89241, d140313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89241, d140313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89242 q = 1) (hb : d140314 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89242, d140314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89242, d140314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89248 q = 1) (hb : d140321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89248, d140321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89248, d140321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25689 q ha hb
  have h13 (q : Pattern) (ha : d89249 q = 1) (hb : d140322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89249, d140322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89249, d140322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89250 q = 1) (hb : d140323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89250, d140323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89250, d140323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89251 q = 1) (hb : d140324 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89251, d140324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89251, d140324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89252 q = 1) (hb : d140325 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89252, d140325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89252, d140325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89253 q = 1) (hb : d140326 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89253, d140326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89253, d140326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25691 (p : Pattern) (ha : d89259 p = 1) (hb : d140332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89254 q = 1) (hb : d140327 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89254, d140327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89254, d140327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25690 q ha hb
  have h2 (q : Pattern) (ha : d89255 q = 1) (hb : d140328 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89255, d140328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89255, d140328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89256 q = 1) (hb : d140329 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89256, d140329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89256, d140329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89257 q = 1) (hb : d140330 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89257, d140330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89257, d140330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89258 q = 1) (hb : d140331 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89258, d140331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89258, d140331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89259 q = 1) (hb : d140332 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89259, d140332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89259, d140332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25692 (p : Pattern) (ha : d89265 p = 1) (hb : d140338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d89150 q = 1) (hb : d140147 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89150, d140147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25661 q ha hb
    | true =>
      simp only [d89150, d140147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25667 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89176 q = 1) (hb : d140192 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89176, d140192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89176, d140192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25673 q ha hb
  have h3 (q : Pattern) (ha : d89177 q = 1) (hb : d140193 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89177, d140193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89177, d140193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89203 q = 1) (hb : d140238 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89203, d140238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89203, d140238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25679 q ha hb
  have h5 (q : Pattern) (ha : d89204 q = 1) (hb : d140239 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89204, d140239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89204, d140239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89205 q = 1) (hb : d140240 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89205, d140240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89205, d140240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89231 q = 1) (hb : d140285 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89231, d140285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89231, d140285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25685 q ha hb
  have h8 (q : Pattern) (ha : d89232 q = 1) (hb : d140286 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89232, d140286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89232, d140286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d89233 q = 1) (hb : d140287 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89233, d140287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89233, d140287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89234 q = 1) (hb : d140288 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d89234, d140288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89234, d140288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d89260 q = 1) (hb : d140333 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89260, d140333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89260, d140333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25691 q ha hb
  have h12 (q : Pattern) (ha : d89261 q = 1) (hb : d140334 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89261, d140334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89261, d140334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89262 q = 1) (hb : d140335 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89262, d140335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89262, d140335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d89263 q = 1) (hb : d140336 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d89263, d140336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89263, d140336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d89264 q = 1) (hb : d140337 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d89264, d140337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89264, d140337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89265 q = 1) (hb : d140338 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d89265, d140338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89265, d140338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro25693 (p : Pattern) (ha : d89271 p = 1) (hb : d140344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89266 q = 1) (hb : d140339 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d89266, d140339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25692 q ha hb
    | true =>
      simp only [d89266, d140339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89267 q = 1) (hb : d140340 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d89267, d140340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89267, d140340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89268 q = 1) (hb : d140341 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d89268, d140341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89268, d140341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89269 q = 1) (hb : d140342 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d89269, d140342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89269, d140342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89270 q = 1) (hb : d140343 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d89270, d140343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89270, d140343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89271 q = 1) (hb : d140344 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d89271, d140344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89271, d140344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25694 (p : Pattern) (ha : d89277 p = 1) (hb : d140350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89272 q = 1) (hb : d140345 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d89272, d140345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25693 q ha hb
    | true =>
      simp only [d89272, d140345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89273 q = 1) (hb : d140346 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d89273, d140346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89273, d140346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89274 q = 1) (hb : d140347 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d89274, d140347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89274, d140347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89275 q = 1) (hb : d140348 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d89275, d140348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89275, d140348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89276 q = 1) (hb : d140349 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d89276, d140349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89276, d140349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89277 q = 1) (hb : d140350 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d89277, d140350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89277, d140350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25695 (p : Pattern) (ha : d89283 p = 1) (hb : d140356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89278 q = 1) (hb : d140351 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d89278, d140351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25694 q ha hb
    | true =>
      simp only [d89278, d140351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89279 q = 1) (hb : d140352 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d89279, d140352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89279, d140352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89280 q = 1) (hb : d140353 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d89280, d140353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89280, d140353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89281 q = 1) (hb : d140354 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d89281, d140354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89281, d140354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89282 q = 1) (hb : d140355 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d89282, d140355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89282, d140355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89283 q = 1) (hb : d140356 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d89283, d140356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89283, d140356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25696 (p : Pattern) (ha : d89289 p = 1) (hb : d140362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89284 q = 1) (hb : d140357 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d89284, d140357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25695 q ha hb
    | true =>
      simp only [d89284, d140357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89285 q = 1) (hb : d140358 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d89285, d140358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89285, d140358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89286 q = 1) (hb : d140359 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d89286, d140359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89286, d140359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89287 q = 1) (hb : d140360 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d89287, d140360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89287, d140360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89288 q = 1) (hb : d140361 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d89288, d140361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89288, d140361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89289 q = 1) (hb : d140362 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d89289, d140362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89289, d140362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25697 (p : Pattern) (ha : d89295 p = 1) (hb : d140368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89290 q = 1) (hb : d140363 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d89290, d140363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25696 q ha hb
    | true =>
      simp only [d89290, d140363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89291 q = 1) (hb : d140364 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d89291, d140364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89291, d140364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89292 q = 1) (hb : d140365 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d89292, d140365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89292, d140365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89293 q = 1) (hb : d140366 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d89293, d140366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89293, d140366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89294 q = 1) (hb : d140367 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d89294, d140367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89294, d140367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89295 q = 1) (hb : d140368 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d89295, d140368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89295, d140368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25698 (p : Pattern) (ha : d89301 p = 1) (hb : d140374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89296 q = 1) (hb : d140369 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d89296, d140369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25697 q ha hb
    | true =>
      simp only [d89296, d140369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89297 q = 1) (hb : d140370 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d89297, d140370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89297, d140370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89298 q = 1) (hb : d140371 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d89298, d140371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89298, d140371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89299 q = 1) (hb : d140372 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d89299, d140372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89299, d140372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89300 q = 1) (hb : d140373 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d89300, d140373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89300, d140373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89301 q = 1) (hb : d140374 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d89301, d140374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89301, d140374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25699 (p : Pattern) (ha : d89307 p = 1) (hb : d140380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89302 q = 1) (hb : d140375 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d89302, d140375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25698 q ha hb
    | true =>
      simp only [d89302, d140375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89303 q = 1) (hb : d140376 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d89303, d140376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89303, d140376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89304 q = 1) (hb : d140377 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d89304, d140377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89304, d140377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89305 q = 1) (hb : d140378 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d89305, d140378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89305, d140378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89306 q = 1) (hb : d140379 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d89306, d140379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89306, d140379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89307 q = 1) (hb : d140380 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d89307, d140380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89307, d140380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25700 (p : Pattern) (ha : d88199 p = 1) (hb : d141016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77924 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80559 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80559, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d80559, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88196 q = 1) (hb : d141013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d141013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d88196, d141013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88197 q = 1) (hb : d141014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d141014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88197, d141014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88198 q = 1) (hb : d141015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d141015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88198, d141015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88199 q = 1) (hb : d141016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88199, d141016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88199, d141016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25701 (p : Pattern) (ha : d88206 p = 1) (hb : d141020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80559 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80559, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d80559, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88196 q = 1) (hb : d141013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88196, d141013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d88196, d141013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88197 q = 1) (hb : d141014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88197, d141014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88197, d141014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88198 q = 1) (hb : d141015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88198, d141015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88198, d141015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d77948 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d77952 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d77954 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80564 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80564, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d80564, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88203 q = 1) (hb : d141017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d141017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d88203, d141017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d88204 q = 1) (hb : d141018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d141018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88204, d141018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88205 q = 1) (hb : d141019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d141019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88205, d141019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88206 q = 1) (hb : d141020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88206, d141020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88206, d141020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25702 (p : Pattern) (ha : d89102 p = 1) (hb : d141027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80564 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80564, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80564, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88203 q = 1) (hb : d141017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88203, d141017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d88203, d141017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88204 q = 1) (hb : d141025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88204, d141025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88204, d141025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88205 q = 1) (hb : d141026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88205, d141026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88205, d141026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89102 q = 1) (hb : d141027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89102, d141027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89102, d141027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25703 (p : Pattern) (ha : d89112 p = 1) (hb : d141036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d80581 q = 1) (hb : d89108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80581, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80581, d89108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89109 q = 1) (hb : d141033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89109, d141033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d89109, d141033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89110 q = 1) (hb : d141034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89110, d141034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89110, d141034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89111 q = 1) (hb : d141035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89111, d141035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89111, d141035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89112 q = 1) (hb : d141036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89112, d141036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89112, d141036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25704 (p : Pattern) (ha : d89118 p = 1) (hb : d141042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77912 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88207 q = 1) (hb : d141021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88207, d141021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25700 q ha hb
    | true =>
      simp only [d88207, d141021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25701 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77964 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88208 q = 1) (hb : d141022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88208, d141022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88208, d141022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89100 q = 1) (hb : d141023 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89100, d141023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89100, d141023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89101 q = 1) (hb : d141024 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89101, d141024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89101, d141024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89103 q = 1) (hb : d141028 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89103, d141028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89103, d141028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25702 q ha hb
  have h8 (q : Pattern) (ha : d89104 q = 1) (hb : d141029 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89104, d141029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89104, d141029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89105 q = 1) (hb : d141030 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89105, d141030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89105, d141030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89106 q = 1) (hb : d141031 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89106, d141031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89106, d141031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89107 q = 1) (hb : d141032 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89107, d141032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89107, d141032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89113 q = 1) (hb : d141037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89113, d141037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89113, d141037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25703 q ha hb
  have h13 (q : Pattern) (ha : d89114 q = 1) (hb : d141038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89114, d141038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89114, d141038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89115 q = 1) (hb : d141039 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89115, d141039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89115, d141039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89116 q = 1) (hb : d141040 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89116, d141040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89116, d141040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89117 q = 1) (hb : d141041 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89117, d141041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89117, d141041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89118 q = 1) (hb : d141042 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89118, d141042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89118, d141042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25705 (p : Pattern) (ha : d89124 p = 1) (hb : d141048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77897 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89119 q = 1) (hb : d141043 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89119, d141043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89119, d141043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25704 q ha hb
  have h3 (q : Pattern) (ha : d89120 q = 1) (hb : d141044 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89120, d141044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89120, d141044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89121 q = 1) (hb : d141045 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89121, d141045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89121, d141045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89122 q = 1) (hb : d141046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89122, d141046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89122, d141046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89123 q = 1) (hb : d141047 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89123, d141047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89123, d141047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89124 q = 1) (hb : d141048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89124, d141048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89124, d141048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25706 (p : Pattern) (ha : d88305 p = 1) (hb : d141053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d139789 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88301 q = 1) (hb : d141049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88301, d141049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88301, d141049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88302 q = 1) (hb : d141050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88302, d141050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88302, d141050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88303 q = 1) (hb : d141051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88303, d141051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88303, d141051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88304 q = 1) (hb : d141052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88304, d141052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88304, d141052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88305 q = 1) (hb : d141053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88305, d141053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88305, d141053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25707 (p : Pattern) (ha : d88314 p = 1) (hb : d141058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78036 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88300 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88301 q = 1) (hb : d141049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88301, d141049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88301, d141049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88302 q = 1) (hb : d141050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88302, d141050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88302, d141050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88303 q = 1) (hb : d141051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88303, d141051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88303, d141051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88304 q = 1) (hb : d141052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88304, d141052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88304, d141052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d139795 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88310 q = 1) (hb : d141054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88310, d141054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88310, d141054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88311 q = 1) (hb : d141055 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88311, d141055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88311, d141055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d88312 q = 1) (hb : d141056 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88312, d141056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88312, d141056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88313 q = 1) (hb : d141057 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88313, d141057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88313, d141057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88314 q = 1) (hb : d141058 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88314, d141058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88314, d141058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25708 (p : Pattern) (ha : d89127 p = 1) (hb : d141065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88309 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88310 q = 1) (hb : d141054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88310, d141054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88310, d141054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88311 q = 1) (hb : d141055 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88311, d141055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88311, d141055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88312 q = 1) (hb : d141063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88312, d141063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88312, d141063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88313 q = 1) (hb : d141064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88313, d141064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88313, d141064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89127 q = 1) (hb : d141065 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89127, d141065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89127, d141065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25709 (p : Pattern) (ha : d89137 p = 1) (hb : d141075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89133 q = 1) (hb : d141071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89133, d141071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89133, d141071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89134 q = 1) (hb : d141072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89134, d141072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89134, d141072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89135 q = 1) (hb : d141073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89135, d141073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89135, d141073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89136 q = 1) (hb : d141074 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89136, d141074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89136, d141074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89137 q = 1) (hb : d141075 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89137, d141075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89137, d141075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25710 (p : Pattern) (ha : d89143 p = 1) (hb : d141081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88315 q = 1) (hb : d141059 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88315, d141059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25706 q ha hb
    | true =>
      simp only [d88315, d141059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25707 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139803 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88316 q = 1) (hb : d141060 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88316, d141060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88316, d141060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89125 q = 1) (hb : d141061 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89125, d141061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89125, d141061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89126 q = 1) (hb : d141062 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89126, d141062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89126, d141062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89128 q = 1) (hb : d141066 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89128, d141066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89128, d141066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25708 q ha hb
  have h8 (q : Pattern) (ha : d89129 q = 1) (hb : d141067 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89129, d141067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89129, d141067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89130 q = 1) (hb : d141068 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89130, d141068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89130, d141068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89131 q = 1) (hb : d141069 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89131, d141069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89131, d141069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89132 q = 1) (hb : d141070 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89132, d141070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89132, d141070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89138 q = 1) (hb : d141076 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89138, d141076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89138, d141076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25709 q ha hb
  have h13 (q : Pattern) (ha : d89139 q = 1) (hb : d141077 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89139, d141077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89139, d141077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89140 q = 1) (hb : d141078 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89140, d141078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89140, d141078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89141 q = 1) (hb : d141079 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89141, d141079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89141, d141079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89142 q = 1) (hb : d141080 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89142, d141080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89142, d141080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89143 q = 1) (hb : d141081 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89143, d141081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89143, d141081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25711 (p : Pattern) (ha : d89149 p = 1) (hb : d141087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89144 q = 1) (hb : d141082 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89144, d141082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89144, d141082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25710 q ha hb
  have h2 (q : Pattern) (ha : d89145 q = 1) (hb : d141083 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89145, d141083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89145, d141083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89146 q = 1) (hb : d141084 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89146, d141084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89146, d141084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89147 q = 1) (hb : d141085 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89147, d141085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89147, d141085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89148 q = 1) (hb : d141086 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89148, d141086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89148, d141086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89149 q = 1) (hb : d141087 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89149, d141087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89149, d141087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25712 (p : Pattern) (ha : d88456 p = 1) (hb : d141093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78189 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d139834 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88452 q = 1) (hb : d141089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88452, d141089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88452, d141089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88453 q = 1) (hb : d141090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88453, d141090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88453, d141090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88454 q = 1) (hb : d141091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88454, d141091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88454, d141091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88455 q = 1) (hb : d141092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88455, d141092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88455, d141092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88456 q = 1) (hb : d141093 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88456, d141093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88456, d141093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25713 (p : Pattern) (ha : d88465 p = 1) (hb : d141098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78183 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88451 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88452 q = 1) (hb : d141089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88452, d141089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88452, d141089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88453 q = 1) (hb : d141090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88453, d141090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88453, d141090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88454 q = 1) (hb : d141091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88454, d141091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88454, d141091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88455 q = 1) (hb : d141092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88455, d141092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88455, d141092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78220 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78224 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d139840 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88461 q = 1) (hb : d141094 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88461, d141094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88461, d141094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88462 q = 1) (hb : d141095 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88462, d141095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88462, d141095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d88463 q = 1) (hb : d141096 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88463, d141096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88463, d141096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88464 q = 1) (hb : d141097 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88464, d141097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88464, d141097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88465 q = 1) (hb : d141098 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88465, d141098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88465, d141098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25714 (p : Pattern) (ha : d89153 p = 1) (hb : d141105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88461 q = 1) (hb : d141094 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88461, d141094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88461, d141094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88462 q = 1) (hb : d141095 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88462, d141095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88462, d141095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88463 q = 1) (hb : d141103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88463, d141103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88463, d141103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88464 q = 1) (hb : d141104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88464, d141104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88464, d141104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89153 q = 1) (hb : d141105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89153, d141105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89153, d141105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25715 (p : Pattern) (ha : d89163 p = 1) (hb : d141115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89159 q = 1) (hb : d141111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89159, d141111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89159, d141111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89160 q = 1) (hb : d141112 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89160, d141112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89160, d141112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89161 q = 1) (hb : d141113 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89161, d141113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89161, d141113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89162 q = 1) (hb : d141114 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89162, d141114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89162, d141114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89163 q = 1) (hb : d141115 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89163, d141115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89163, d141115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25716 (p : Pattern) (ha : d89169 p = 1) (hb : d141121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78177 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88466 q = 1) (hb : d141099 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88466, d141099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25712 q ha hb
    | true =>
      simp only [d88466, d141099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25713 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88467 q = 1) (hb : d141100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88467, d141100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88467, d141100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89151 q = 1) (hb : d141101 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89151, d141101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89151, d141101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89152 q = 1) (hb : d141102 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89152, d141102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89152, d141102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89154 q = 1) (hb : d141106 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89154, d141106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89154, d141106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25714 q ha hb
  have h8 (q : Pattern) (ha : d89155 q = 1) (hb : d141107 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89155, d141107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89155, d141107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89156 q = 1) (hb : d141108 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89156, d141108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89156, d141108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89157 q = 1) (hb : d141109 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89157, d141109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89157, d141109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89158 q = 1) (hb : d141110 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89158, d141110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89158, d141110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89164 q = 1) (hb : d141116 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89164, d141116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89164, d141116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25715 q ha hb
  have h13 (q : Pattern) (ha : d89165 q = 1) (hb : d141117 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89165, d141117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89165, d141117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89166 q = 1) (hb : d141118 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89166, d141118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89166, d141118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89167 q = 1) (hb : d141119 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89167, d141119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89167, d141119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89168 q = 1) (hb : d141120 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89168, d141120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89168, d141120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89169 q = 1) (hb : d141121 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89169, d141121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89169, d141121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25717 (p : Pattern) (ha : d89175 p = 1) (hb : d141127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89170 q = 1) (hb : d141122 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89170, d141122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89170, d141122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25716 q ha hb
  have h2 (q : Pattern) (ha : d89171 q = 1) (hb : d141123 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89171, d141123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89171, d141123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89172 q = 1) (hb : d141124 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89172, d141124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89172, d141124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89173 q = 1) (hb : d141125 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89173, d141125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89173, d141125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89174 q = 1) (hb : d141126 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89174, d141126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89174, d141126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89175 q = 1) (hb : d141127 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89175, d141127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89175, d141127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25718 (p : Pattern) (ha : d88608 p = 1) (hb : d141134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d139880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88604 q = 1) (hb : d141130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88604, d141130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88604, d141130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88605 q = 1) (hb : d141131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88605, d141131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88605, d141131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88606 q = 1) (hb : d141132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88606, d141132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88606, d141132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88607 q = 1) (hb : d141133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88607, d141133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88607, d141133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88608 q = 1) (hb : d141134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88608, d141134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88608, d141134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25719 (p : Pattern) (ha : d88617 p = 1) (hb : d141139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78337 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88603 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88604 q = 1) (hb : d141130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88604, d141130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88604, d141130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88605 q = 1) (hb : d141131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88605, d141131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88605, d141131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88606 q = 1) (hb : d141132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88606, d141132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88606, d141132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88607 q = 1) (hb : d141133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88607, d141133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88607, d141133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78368 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78372 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d139886 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88613 q = 1) (hb : d141135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88613, d141135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88613, d141135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88614 q = 1) (hb : d141136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88614, d141136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88614, d141136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d88615 q = 1) (hb : d141137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88615, d141137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88615, d141137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88616 q = 1) (hb : d141138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88616, d141138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88616, d141138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88617 q = 1) (hb : d141139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88617, d141139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88617, d141139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25720 (p : Pattern) (ha : d89180 p = 1) (hb : d141146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88613 q = 1) (hb : d141135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88613, d141135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88613, d141135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88614 q = 1) (hb : d141136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88614, d141136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88614, d141136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88615 q = 1) (hb : d141144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88615, d141144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88615, d141144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88616 q = 1) (hb : d141145 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88616, d141145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88616, d141145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89180 q = 1) (hb : d141146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89180, d141146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89180, d141146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25721 (p : Pattern) (ha : d89190 p = 1) (hb : d141156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89186 q = 1) (hb : d141152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89186, d141152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89186, d141152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89187 q = 1) (hb : d141153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89187, d141153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89187, d141153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89188 q = 1) (hb : d141154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89188, d141154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89188, d141154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89189 q = 1) (hb : d141155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89189, d141155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89189, d141155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89190 q = 1) (hb : d141156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89190, d141156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89190, d141156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25722 (p : Pattern) (ha : d89196 p = 1) (hb : d141162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78325 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88618 q = 1) (hb : d141140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88618, d141140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25718 q ha hb
    | true =>
      simp only [d88618, d141140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25719 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88619 q = 1) (hb : d141141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88619, d141141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88619, d141141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89178 q = 1) (hb : d141142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89178, d141142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89178, d141142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89179 q = 1) (hb : d141143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89179, d141143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89179, d141143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89181 q = 1) (hb : d141147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89181, d141147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89181, d141147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25720 q ha hb
  have h8 (q : Pattern) (ha : d89182 q = 1) (hb : d141148 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89182, d141148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89182, d141148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89183 q = 1) (hb : d141149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89183, d141149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89183, d141149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89184 q = 1) (hb : d141150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89184, d141150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89184, d141150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89185 q = 1) (hb : d141151 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89185, d141151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89185, d141151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89191 q = 1) (hb : d141157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89191, d141157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89191, d141157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25721 q ha hb
  have h13 (q : Pattern) (ha : d89192 q = 1) (hb : d141158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89192, d141158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89192, d141158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89193 q = 1) (hb : d141159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89193, d141159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89193, d141159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89194 q = 1) (hb : d141160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89194, d141160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89194, d141160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89195 q = 1) (hb : d141161 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89195, d141161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89195, d141161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89196 q = 1) (hb : d141162 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89196, d141162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89196, d141162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25723 (p : Pattern) (ha : d89202 p = 1) (hb : d141168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89197 q = 1) (hb : d141163 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89197, d141163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89197, d141163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25722 q ha hb
  have h2 (q : Pattern) (ha : d89198 q = 1) (hb : d141164 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89198, d141164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89198, d141164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89199 q = 1) (hb : d141165 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89199, d141165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89199, d141165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89200 q = 1) (hb : d141166 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89200, d141166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89200, d141166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89201 q = 1) (hb : d141167 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89201, d141167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89201, d141167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89202 q = 1) (hb : d141168 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89202, d141168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89202, d141168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25724 (p : Pattern) (ha : d88761 p = 1) (hb : d141176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78486 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d139927 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88757 q = 1) (hb : d141172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88757, d141172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88757, d141172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88758 q = 1) (hb : d141173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88758, d141173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88758, d141173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88759 q = 1) (hb : d141174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88759, d141174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88759, d141174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88760 q = 1) (hb : d141175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88760, d141175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88760, d141175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88761 q = 1) (hb : d141176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88761, d141176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88761, d141176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25725 (p : Pattern) (ha : d88770 p = 1) (hb : d141181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78480 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78486 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88756 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88757 q = 1) (hb : d141172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88757, d141172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88757, d141172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88758 q = 1) (hb : d141173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88758, d141173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88758, d141173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88759 q = 1) (hb : d141174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88759, d141174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88759, d141174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88760 q = 1) (hb : d141175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88760, d141175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88760, d141175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78517 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78521 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d139933 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88766 q = 1) (hb : d141177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88766, d141177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88766, d141177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88767 q = 1) (hb : d141178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88767, d141178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88767, d141178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d88768 q = 1) (hb : d141179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88768, d141179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88768, d141179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88769 q = 1) (hb : d141180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88769, d141180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88769, d141180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88770 q = 1) (hb : d141181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88770, d141181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88770, d141181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25726 (p : Pattern) (ha : d89208 p = 1) (hb : d141188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88765 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88766 q = 1) (hb : d141177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88766, d141177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88766, d141177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88767 q = 1) (hb : d141178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88767, d141178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88767, d141178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88768 q = 1) (hb : d141186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88768, d141186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88768, d141186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88769 q = 1) (hb : d141187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88769, d141187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88769, d141187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89208 q = 1) (hb : d141188 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89208, d141188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89208, d141188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25727 (p : Pattern) (ha : d89218 p = 1) (hb : d141198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89214 q = 1) (hb : d141194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89214, d141194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89214, d141194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89215 q = 1) (hb : d141195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89215, d141195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89215, d141195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89216 q = 1) (hb : d141196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89216, d141196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89216, d141196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89217 q = 1) (hb : d141197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89217, d141197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89217, d141197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89218 q = 1) (hb : d141198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89218, d141198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89218, d141198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25728 (p : Pattern) (ha : d89224 p = 1) (hb : d141204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78474 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88771 q = 1) (hb : d141182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88771, d141182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25724 q ha hb
    | true =>
      simp only [d88771, d141182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25725 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88772 q = 1) (hb : d141183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88772, d141183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88772, d141183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89206 q = 1) (hb : d141184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89206, d141184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89206, d141184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89207 q = 1) (hb : d141185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89207, d141185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89207, d141185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89209 q = 1) (hb : d141189 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89209, d141189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89209, d141189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25726 q ha hb
  have h8 (q : Pattern) (ha : d89210 q = 1) (hb : d141190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89210, d141190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89210, d141190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89211 q = 1) (hb : d141191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89211, d141191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89211, d141191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89212 q = 1) (hb : d141192 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89212, d141192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89212, d141192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89213 q = 1) (hb : d141193 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89213, d141193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89213, d141193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89219 q = 1) (hb : d141199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89219, d141199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89219, d141199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25727 q ha hb
  have h13 (q : Pattern) (ha : d89220 q = 1) (hb : d141200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89220, d141200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89220, d141200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89221 q = 1) (hb : d141201 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89221, d141201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89221, d141201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89222 q = 1) (hb : d141202 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89222, d141202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89222, d141202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89223 q = 1) (hb : d141203 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89223, d141203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89223, d141203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89224 q = 1) (hb : d141204 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89224, d141204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89224, d141204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25729 (p : Pattern) (ha : d89230 p = 1) (hb : d141210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89225 q = 1) (hb : d141205 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89225, d141205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89225, d141205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25728 q ha hb
  have h2 (q : Pattern) (ha : d89226 q = 1) (hb : d141206 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89226, d141206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89226, d141206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89227 q = 1) (hb : d141207 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89227, d141207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89227, d141207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89228 q = 1) (hb : d141208 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89228, d141208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89228, d141208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89229 q = 1) (hb : d141209 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89229, d141209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89229, d141209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89230 q = 1) (hb : d141210 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89230, d141210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89230, d141210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25730 (p : Pattern) (ha : d88915 p = 1) (hb : d141219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78636 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d139975 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d88911 q = 1) (hb : d141215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88911, d141215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88911, d141215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88912 q = 1) (hb : d141216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88912, d141216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d88912, d141216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d88913 q = 1) (hb : d141217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88913, d141217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88913, d141217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88914 q = 1) (hb : d141218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88914, d141218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88914, d141218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d88915 q = 1) (hb : d141219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88915, d141219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88915, d141219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25731 (p : Pattern) (ha : d88924 p = 1) (hb : d141224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78630 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d78636 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d88910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d88911 q = 1) (hb : d141215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88911, d141215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88911, d141215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d88912 q = 1) (hb : d141216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88912, d141216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88912, d141216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88913 q = 1) (hb : d141217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88913, d141217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88913, d141217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88914 q = 1) (hb : d141218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88914, d141218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88914, d141218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78667 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d78671 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d139981 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d88920 q = 1) (hb : d141220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88920, d141220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88920, d141220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d88921 q = 1) (hb : d141221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88921, d141221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88921, d141221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h15 (q : Pattern) (ha : d88922 q = 1) (hb : d141222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88922, d141222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88922, d141222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88923 q = 1) (hb : d141223 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88923, d141223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d88923, d141223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d88924 q = 1) (hb : d141224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88924, d141224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88924, d141224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25732 (p : Pattern) (ha : d89237 p = 1) (hb : d141231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d139981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d88919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88920 q = 1) (hb : d141220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d88920, d141220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88920, d141220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d88921 q = 1) (hb : d141221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88921, d141221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88921, d141221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88922 q = 1) (hb : d141229 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88922, d141229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88922, d141229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88923 q = 1) (hb : d141230 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88923, d141230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88923, d141230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89237 q = 1) (hb : d141231 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89237, d141231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89237, d141231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25733 (p : Pattern) (ha : d89247 p = 1) (hb : d141241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140001 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d89034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d89243 q = 1) (hb : d141237 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89243, d141237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89243, d141237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d89244 q = 1) (hb : d141238 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89244, d141238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89244, d141238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89245 q = 1) (hb : d141239 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89245, d141239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89245, d141239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89246 q = 1) (hb : d141240 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89246, d141240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89246, d141240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89247 q = 1) (hb : d141241 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89247, d141241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89247, d141241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25734 (p : Pattern) (ha : d89253 p = 1) (hb : d141247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d78624 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88925 q = 1) (hb : d141225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88925, d141225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25730 q ha hb
    | true =>
      simp only [d88925, d141225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25731 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d88926 q = 1) (hb : d141226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88926, d141226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d88926, d141226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d89235 q = 1) (hb : d141227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89235, d141227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89235, d141227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89236 q = 1) (hb : d141228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89236, d141228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89236, d141228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89238 q = 1) (hb : d141232 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89238, d141232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89238, d141232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25732 q ha hb
  have h8 (q : Pattern) (ha : d89239 q = 1) (hb : d141233 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89239, d141233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d89239, d141233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d89240 q = 1) (hb : d141234 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89240, d141234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d89240, d141234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d89241 q = 1) (hb : d141235 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89241, d141235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d89241, d141235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d89242 q = 1) (hb : d141236 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89242, d141236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89242, d141236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89248 q = 1) (hb : d141242 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89248, d141242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89248, d141242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25733 q ha hb
  have h13 (q : Pattern) (ha : d89249 q = 1) (hb : d141243 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89249, d141243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d89249, d141243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d89250 q = 1) (hb : d141244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89250, d141244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89250, d141244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d89251 q = 1) (hb : d141245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89251, d141245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d89251, d141245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d89252 q = 1) (hb : d141246 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89252, d141246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89252, d141246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d89253 q = 1) (hb : d141247 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89253, d141247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d89253, d141247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro25735 (p : Pattern) (ha : d89259 p = 1) (hb : d141253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89254 q = 1) (hb : d141248 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89254, d141248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89254, d141248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25734 q ha hb
  have h2 (q : Pattern) (ha : d89255 q = 1) (hb : d141249 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89255, d141249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89255, d141249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89256 q = 1) (hb : d141250 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89256, d141250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89256, d141250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89257 q = 1) (hb : d141251 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89257, d141251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89257, d141251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89258 q = 1) (hb : d141252 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89258, d141252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89258, d141252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89259 q = 1) (hb : d141253 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89259, d141253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89259, d141253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25736 (p : Pattern) (ha : d89265 p = 1) (hb : d141259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d89150 q = 1) (hb : d141088 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89150, d141088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25705 q ha hb
    | true =>
      simp only [d89150, d141088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25711 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89176 q = 1) (hb : d141128 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89176, d141128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89176, d141128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25717 q ha hb
  have h3 (q : Pattern) (ha : d89177 q = 1) (hb : d141129 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89177, d141129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89177, d141129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89203 q = 1) (hb : d141169 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89203, d141169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89203, d141169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25723 q ha hb
  have h5 (q : Pattern) (ha : d89204 q = 1) (hb : d141170 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89204, d141170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89204, d141170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89205 q = 1) (hb : d141171 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89205, d141171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89205, d141171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d89231 q = 1) (hb : d141211 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89231, d141211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89231, d141211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25729 q ha hb
  have h8 (q : Pattern) (ha : d89232 q = 1) (hb : d141212 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89232, d141212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89232, d141212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d89233 q = 1) (hb : d141213 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89233, d141213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89233, d141213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89234 q = 1) (hb : d141214 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d89234, d141214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89234, d141214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d89260 q = 1) (hb : d141254 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d89260, d141254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89260, d141254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25735 q ha hb
  have h12 (q : Pattern) (ha : d89261 q = 1) (hb : d141255 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d89261, d141255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89261, d141255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89262 q = 1) (hb : d141256 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d89262, d141256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89262, d141256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d89263 q = 1) (hb : d141257 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d89263, d141257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89263, d141257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d89264 q = 1) (hb : d141258 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d89264, d141258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89264, d141258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d89265 q = 1) (hb : d141259 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d89265, d141259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d89265, d141259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro25737 (p : Pattern) (ha : d89271 p = 1) (hb : d141265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89266 q = 1) (hb : d141260 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d89266, d141260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25736 q ha hb
    | true =>
      simp only [d89266, d141260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89267 q = 1) (hb : d141261 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d89267, d141261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89267, d141261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89268 q = 1) (hb : d141262 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d89268, d141262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89268, d141262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89269 q = 1) (hb : d141263 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d89269, d141263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89269, d141263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89270 q = 1) (hb : d141264 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d89270, d141264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89270, d141264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89271 q = 1) (hb : d141265 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d89271, d141265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89271, d141265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25738 (p : Pattern) (ha : d89277 p = 1) (hb : d141271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89272 q = 1) (hb : d141266 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d89272, d141266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25737 q ha hb
    | true =>
      simp only [d89272, d141266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89273 q = 1) (hb : d141267 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d89273, d141267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89273, d141267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89274 q = 1) (hb : d141268 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d89274, d141268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89274, d141268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89275 q = 1) (hb : d141269 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d89275, d141269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89275, d141269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89276 q = 1) (hb : d141270 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d89276, d141270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89276, d141270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89277 q = 1) (hb : d141271 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d89277, d141271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89277, d141271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25739 (p : Pattern) (ha : d89283 p = 1) (hb : d141277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89278 q = 1) (hb : d141272 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d89278, d141272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25738 q ha hb
    | true =>
      simp only [d89278, d141272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89279 q = 1) (hb : d141273 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d89279, d141273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89279, d141273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89280 q = 1) (hb : d141274 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d89280, d141274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89280, d141274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89281 q = 1) (hb : d141275 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d89281, d141275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89281, d141275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89282 q = 1) (hb : d141276 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d89282, d141276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89282, d141276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89283 q = 1) (hb : d141277 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d89283, d141277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89283, d141277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25740 (p : Pattern) (ha : d89289 p = 1) (hb : d141283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89284 q = 1) (hb : d141278 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d89284, d141278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25739 q ha hb
    | true =>
      simp only [d89284, d141278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89285 q = 1) (hb : d141279 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d89285, d141279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89285, d141279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89286 q = 1) (hb : d141280 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d89286, d141280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89286, d141280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89287 q = 1) (hb : d141281 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d89287, d141281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89287, d141281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89288 q = 1) (hb : d141282 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d89288, d141282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89288, d141282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89289 q = 1) (hb : d141283 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d89289, d141283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89289, d141283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25741 (p : Pattern) (ha : d89295 p = 1) (hb : d141289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89290 q = 1) (hb : d141284 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d89290, d141284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25740 q ha hb
    | true =>
      simp only [d89290, d141284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89291 q = 1) (hb : d141285 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d89291, d141285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89291, d141285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89292 q = 1) (hb : d141286 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d89292, d141286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89292, d141286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89293 q = 1) (hb : d141287 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d89293, d141287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89293, d141287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89294 q = 1) (hb : d141288 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d89294, d141288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89294, d141288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89295 q = 1) (hb : d141289 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d89295, d141289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89295, d141289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25742 (p : Pattern) (ha : d89301 p = 1) (hb : d141295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89296 q = 1) (hb : d141290 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d89296, d141290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25741 q ha hb
    | true =>
      simp only [d89296, d141290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89297 q = 1) (hb : d141291 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d89297, d141291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89297, d141291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89298 q = 1) (hb : d141292 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d89298, d141292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89298, d141292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89299 q = 1) (hb : d141293 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d89299, d141293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89299, d141293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89300 q = 1) (hb : d141294 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d89300, d141294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89300, d141294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89301 q = 1) (hb : d141295 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d89301, d141295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89301, d141295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25743 (p : Pattern) (ha : d89307 p = 1) (hb : d141301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89302 q = 1) (hb : d141296 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d89302, d141296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25742 q ha hb
    | true =>
      simp only [d89302, d141296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89303 q = 1) (hb : d141297 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d89303, d141297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d89303, d141297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d89304 q = 1) (hb : d141298 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d89304, d141298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d89304, d141298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d89305 q = 1) (hb : d141299 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d89305, d141299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89305, d141299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89306 q = 1) (hb : d141300 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d89306, d141300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89306, d141300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d89307 q = 1) (hb : d141301 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d89307, d141301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d89307, d141301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25744 (p : Pattern) (ha : d10654 p = 1) (hb : d112686 p = 1) : d141304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d112686 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10652 q = 1) (hb : d112686 q = 1) : d141302 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10652, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d112686 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10653 q = 1) (hb : d112686 q = 1) : d141303 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d141303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10653, d141303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10654 q = 1) (hb : d112686 q = 1) : d141304 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d141304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10654, d141304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro25745 (p : Pattern) (ha : d10660 p = 1) (hb : d112686 p = 1) : d141310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112686 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d112686 q = 1) : d141307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d112686 q = 1) : d141308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d112686 q = 1) : d141309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10660 q = 1) (hb : d112686 q = 1) : d141310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d141310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d141310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25746 (p : Pattern) (ha : d108784 p = 1) (hb : d112686 p = 1) : d141316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d112686 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d112686 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d112686 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10661 q = 1) (hb : d112686 q = 1) : d141311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
    | true =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108780 q = 1) (hb : d112686 q = 1) : d141312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108780, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d112686 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108781 q = 1) (hb : d112686 q = 1) : d141313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108782 q = 1) (hb : d112686 q = 1) : d141314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108782, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108783 q = 1) (hb : d112686 q = 1) : d141315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108783, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108784 q = 1) (hb : d112686 q = 1) : d141316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108784, d141316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108784, d141316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25747 (p : Pattern) (ha : d10667 p = 1) (hb : d112686 p = 1) : d141317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d112686 q = 1) : d141305 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25744 q ha hb
    | true =>
      simp only [d10655, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d112686 q = 1) : d141306 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d112686 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d112686 q = 1) : d141307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d112686 q = 1) : d141308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d112686 q = 1) : d141309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d141309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10667 q = 1) (hb : d112686 q = 1) : d141317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d141317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10667, d141317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25748 (p : Pattern) (ha : d108789 p = 1) (hb : d112686 p = 1) : d141323 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d112686 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d112686 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d112686 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10661 q = 1) (hb : d112686 q = 1) : d141311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25745 q ha hb
    | true =>
      simp only [d10661, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108780 q = 1) (hb : d112686 q = 1) : d141312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108780, d141312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d112686 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108781 q = 1) (hb : d112686 q = 1) : d141313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d141313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108782 q = 1) (hb : d112686 q = 1) : d141314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108782, d141314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108783 q = 1) (hb : d112686 q = 1) : d141315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108783, d141315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d112686 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d112686 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d112686 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10668 q = 1) (hb : d112686 q = 1) : d141318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25747 q ha hb
    | true =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108785 q = 1) (hb : d112686 q = 1) : d141319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108785, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d112686 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108786 q = 1) (hb : d112686 q = 1) : d141320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108786, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108787 q = 1) (hb : d112686 q = 1) : d141321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108787, d141321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108787, d141321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108788 q = 1) (hb : d112686 q = 1) : d141322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108788, d141322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108788, d141322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d108789 q = 1) (hb : d112686 q = 1) : d141323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108789, d141323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108789, d141323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25749 (p : Pattern) (ha : d108796 p = 1) (hb : d112686 p = 1) : d141330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d112686 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d112686 q = 1) : d141318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25747 q ha hb
    | true =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108785 q = 1) (hb : d112686 q = 1) : d141319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108785, d141319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d112686 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108786 q = 1) (hb : d112686 q = 1) : d141320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108786, d141320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108794 q = 1) (hb : d112686 q = 1) : d141328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108794, d141328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108794, d141328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108795 q = 1) (hb : d112686 q = 1) : d141329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108795, d141329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108795, d141329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108796 q = 1) (hb : d112686 q = 1) : d141330 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108796, d141330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108796, d141330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
