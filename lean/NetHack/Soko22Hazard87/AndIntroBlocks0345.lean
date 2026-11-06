import NetHack.Soko22Hazard87.AndIntroBlocks0344
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro86250 (p : Pattern) (ha : d47080 p = 1) (hb : d320345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47066 q = 1) (hb : d320331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, d320331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86246 q ha hb
    | true =>
      simp only [d47066, d320331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47067 q = 1) (hb : d320332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, d320332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47067, d320332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47068 q = 1) (hb : d320333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, d320333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47068, d320333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47069 q = 1) (hb : d320334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, d320334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47069, d320334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47070 q = 1) (hb : d320335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, d320335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47070, d320335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47080 q = 1) (hb : d320345 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47080, d320345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47080, d320345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86251 (p : Pattern) (ha : d47096 p = 1) (hb : d320361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d320351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d320352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d320353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d320354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47090 q = 1) (hb : d320355 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47095 q = 1) (hb : d320360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47096 q = 1) (hb : d320361 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, d320361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47096, d320361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro86252 (p : Pattern) (ha : d47106 p = 1) (hb : d320371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d320351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d320352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d320353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d320354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d320360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d320366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86238 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d320207 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86238 q ha hb
    | true =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d320367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46890 q = 1) (hb : d320208 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, d320208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46890, d320208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47103 q = 1) (hb : d320368 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, d320368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47103, d320368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47104 q = 1) (hb : d320369 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, d320369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47104, d320369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d47105 q = 1) (hb : d320370 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, d320370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47105, d320370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d47106 q = 1) (hb : d320371 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, d320371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47106, d320371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86253 (p : Pattern) (ha : d47125 p = 1) (hb : d320390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47107 q = 1) (hb : d320372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86252 q ha hb
  have h2 (q : Pattern) (ha : d47108 q = 1) (hb : d320373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47109 q = 1) (hb : d320374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47115 q = 1) (hb : d320380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47124 q = 1) (hb : d320389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47124, d320389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47124, d320389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47125 q = 1) (hb : d320390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47125, d320390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47125, d320390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86254 (p : Pattern) (ha : d47216 p = 1) (hb : d320447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47126 q = 1) (hb : d320391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86253 q ha hb
    | true =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47127 q = 1) (hb : d320392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47213 q = 1) (hb : d320444 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47213, d320444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47213, d320444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47214 q = 1) (hb : d320445 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47214, d320445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47214, d320445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47215 q = 1) (hb : d320446 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47215, d320446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47215, d320446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47216 q = 1) (hb : d320447 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47216, d320447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47216, d320447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86255 (p : Pattern) (ha : d47222 p = 1) (hb : d320453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47217 q = 1) (hb : d320448 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47217, d320448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86254 q ha hb
    | true =>
      simp only [d47217, d320448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47218 q = 1) (hb : d320449 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47218, d320449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47218, d320449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47219 q = 1) (hb : d320450 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47219, d320450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47219, d320450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47220 q = 1) (hb : d320451 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47220, d320451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47220, d320451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47221 q = 1) (hb : d320452 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47221, d320452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47221, d320452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47222 q = 1) (hb : d320453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47222, d320453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47222, d320453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86256 (p : Pattern) (ha : d46936 p = 1) (hb : d320254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d320220 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86240 q ha hb
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d320221 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d320226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d320227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46935 q = 1) (hb : d320253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46936 q = 1) (hb : d320254 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46936, d320254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46936, d320254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86257 (p : Pattern) (ha : d46938 p = 1) (hb : d320256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d320230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46913 q = 1) (hb : d320231 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46937 q = 1) (hb : d320255 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46938 q = 1) (hb : d320256 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46938, d320256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46938, d320256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86258 (p : Pattern) (ha : d46945 p = 1) (hb : d320263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d320220 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86240 q ha hb
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d320221 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d320226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46943 q = 1) (hb : d320261 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46944 q = 1) (hb : d320262 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46945 q = 1) (hb : d320263 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46945, d320263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46945, d320263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86259 (p : Pattern) (ha : d46948 p = 1) (hb : d320266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d320230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46946 q = 1) (hb : d320264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46947 q = 1) (hb : d320265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46948 q = 1) (hb : d320266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46948, d320266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46948, d320266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86260 (p : Pattern) (ha : d46957 p = 1) (hb : d320275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46952 q = 1) (hb : d320270 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46952, d320270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46952, d320270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86236 q ha hb
  have h2 (q : Pattern) (ha : d46953 q = 1) (hb : d320271 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46953, d320271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46953, d320271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46954 q = 1) (hb : d320272 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46954, d320272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46954, d320272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46885 q = 1) (hb : d320203 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86236 q ha hb
    | true =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86237 q ha hb
  have h5 (q : Pattern) (ha : d46886 q = 1) (hb : d320204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46887 q = 1) (hb : d320205 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46955 q = 1) (hb : d320273 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46955, d320273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46955, d320273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46895 q = 1) (hb : d320213 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86237 q ha hb
    | true =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86239 q ha hb
  have h9 (q : Pattern) (ha : d46896 q = 1) (hb : d320214 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46897 q = 1) (hb : d320215 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46898 q = 1) (hb : d320216 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46956 q = 1) (hb : d320274 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46956, d320274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46956, d320274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46957 q = 1) (hb : d320275 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46957, d320275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46957, d320275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro86261 (p : Pattern) (ha : d46963 p = 1) (hb : d320281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46958 q = 1) (hb : d320276 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86260 q ha hb
    | true =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46959 q = 1) (hb : d320277 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46902 q = 1) (hb : d320220 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86240 q ha hb
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46903 q = 1) (hb : d320221 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46960 q = 1) (hb : d320278 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46961 q = 1) (hb : d320279 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46962 q = 1) (hb : d320280 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46963 q = 1) (hb : d320281 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46963, d320281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46963, d320281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86262 (p : Pattern) (ha : d47016 p = 1) (hb : d320284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46879 q = 1) (hb : d320197 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46879, d320197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46880 q = 1) (hb : d320198 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, d320198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46881 q = 1) (hb : d320199 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46881, d320199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47016 q = 1) (hb : d320284 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47016, d320284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47016, d320284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86263 (p : Pattern) (ha : d47022 p = 1) (hb : d320290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46885 q = 1) (hb : d320203 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86236 q ha hb
    | true =>
      simp only [d46885, d320203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86237 q ha hb
  have h2 (q : Pattern) (ha : d46886 q = 1) (hb : d320204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46886, d320204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46887 q = 1) (hb : d320205 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46887, d320205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46895 q = 1) (hb : d320213 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86237 q ha hb
    | true =>
      simp only [d46895, d320213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86239 q ha hb
  have h5 (q : Pattern) (ha : d46896 q = 1) (hb : d320214 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46896, d320214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46897 q = 1) (hb : d320215 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46897, d320215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46898 q = 1) (hb : d320216 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, d320216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47017 q = 1) (hb : d320285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47017, d320285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86262 q ha hb
    | true =>
      simp only [d47017, d320285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47018 q = 1) (hb : d320286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47018, d320286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47018, d320286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47019 q = 1) (hb : d320287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47019, d320287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47019, d320287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47020 q = 1) (hb : d320288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47020, d320288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47020, d320288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47021 q = 1) (hb : d320289 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47021, d320289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47021, d320289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47022 q = 1) (hb : d320290 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47022, d320290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47022, d320290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro86264 (p : Pattern) (ha : d47028 p = 1) (hb : d320296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47023 q = 1) (hb : d320291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86263 q ha hb
    | true =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47024 q = 1) (hb : d320292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47025 q = 1) (hb : d320293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47026 q = 1) (hb : d320294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47027 q = 1) (hb : d320295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47028 q = 1) (hb : d320296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47028, d320296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47028, d320296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86265 (p : Pattern) (ha : d320302 p = 1) (hb : d321686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46939 q = 1) (hb : d320257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86256 q ha hb
    | true =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86257 q ha hb
  have h2 (q : Pattern) (ha : d46940 q = 1) (hb : d320258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46941 q = 1) (hb : d320259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46942 q = 1) (hb : d320260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46949 q = 1) (hb : d320267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86258 q ha hb
    | true =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86259 q ha hb
  have h6 (q : Pattern) (ha : d46950 q = 1) (hb : d320268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46951 q = 1) (hb : d320269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46964 q = 1) (hb : d320282 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86261 q ha hb
    | true =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86242 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d320234 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d320283 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320283, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d320283, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d47029 q = 1) (hb : d320297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86264 q ha hb
    | true =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47030 q = 1) (hb : d320298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d320299 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320299, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320299, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d320300 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320300, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d320300, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320301 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320301, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320301, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320302 q = 1) (hb : d321686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320302, d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320302, d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro86266 (p : Pattern) (ha : d47035 p = 1) (hb : d320303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d320220 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86240 q ha hb
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d320221 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d320226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46909 q = 1) (hb : d320227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, d320227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46935 q = 1) (hb : d320253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46935, d320253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47035 q = 1) (hb : d320303 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47035, d320303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47035, d320303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86267 (p : Pattern) (ha : d47036 p = 1) (hb : d320304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d320230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46913 q = 1) (hb : d320231 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, d320231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46937 q = 1) (hb : d320255 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46937, d320255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47036 q = 1) (hb : d320304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47036, d320304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47036, d320304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86268 (p : Pattern) (ha : d47041 p = 1) (hb : d320309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46902 q = 1) (hb : d320220 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86240 q ha hb
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46903 q = 1) (hb : d320221 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46908 q = 1) (hb : d320226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, d320226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46943 q = 1) (hb : d320261 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46943, d320261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46944 q = 1) (hb : d320262 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, d320262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47041 q = 1) (hb : d320309 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47041, d320309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47041, d320309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86269 (p : Pattern) (ha : d47042 p = 1) (hb : d320310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46906 q = 1) (hb : d320224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86241 q ha hb
    | true =>
      simp only [d46906, d320224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46907 q = 1) (hb : d320225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46907, d320225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46912 q = 1) (hb : d320230 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, d320230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46946 q = 1) (hb : d320264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46946, d320264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46947 q = 1) (hb : d320265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, d320265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47042 q = 1) (hb : d320310 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47042, d320310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47042, d320310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86270 (p : Pattern) (ha : d47046 p = 1) (hb : d320314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46958 q = 1) (hb : d320276 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86260 q ha hb
    | true =>
      simp only [d46958, d320276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46959 q = 1) (hb : d320277 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46959, d320277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46902 q = 1) (hb : d320220 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86240 q ha hb
    | true =>
      simp only [d46902, d320220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46903 q = 1) (hb : d320221 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46903, d320221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46960 q = 1) (hb : d320278 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46960, d320278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46961 q = 1) (hb : d320279 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46961, d320279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46962 q = 1) (hb : d320280 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46962, d320280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47046 q = 1) (hb : d320314 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47046, d320314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47046, d320314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86271 (p : Pattern) (ha : d47052 p = 1) (hb : d320317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47023 q = 1) (hb : d320291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86263 q ha hb
    | true =>
      simp only [d47023, d320291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47024 q = 1) (hb : d320292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47024, d320292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47025 q = 1) (hb : d320293 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47025, d320293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47026 q = 1) (hb : d320294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47026, d320294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47027 q = 1) (hb : d320295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47027, d320295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47052 q = 1) (hb : d320317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47052, d320317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47052, d320317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86272 (p : Pattern) (ha : d320323 p = 1) (hb : d321691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46939 q = 1) (hb : d320257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86256 q ha hb
    | true =>
      simp only [d46939, d320257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86257 q ha hb
  have h2 (q : Pattern) (ha : d46940 q = 1) (hb : d320258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46940, d320258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46941 q = 1) (hb : d320259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46941, d320259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46942 q = 1) (hb : d320260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46942, d320260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46949 q = 1) (hb : d320267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86258 q ha hb
    | true =>
      simp only [d46949, d320267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86259 q ha hb
  have h6 (q : Pattern) (ha : d46950 q = 1) (hb : d320268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46950, d320268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46951 q = 1) (hb : d320269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46951, d320269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46964 q = 1) (hb : d320282 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86261 q ha hb
    | true =>
      simp only [d46964, d320282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86242 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d320234 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d320283 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320283, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d320283, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d47029 q = 1) (hb : d320297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86264 q ha hb
    | true =>
      simp only [d47029, d320297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47030 q = 1) (hb : d320298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d47030, d320298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d320299 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320299, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320299, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d320300 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320300, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d320300, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320301 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320301, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320301, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d47037 q = 1) (hb : d320305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47037, d320305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86266 q ha hb
    | true =>
      simp only [d47037, d320305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86267 q ha hb
  have h17 (q : Pattern) (ha : d47038 q = 1) (hb : d320306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47038, d320306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47038, d320306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d47039 q = 1) (hb : d320307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47039, d320307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d47039, d320307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d47040 q = 1) (hb : d320308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47040, d320308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47040, d320308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d47043 q = 1) (hb : d320311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47043, d320311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86268 q ha hb
    | true =>
      simp only [d47043, d320311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86269 q ha hb
  have h21 (q : Pattern) (ha : d47044 q = 1) (hb : d320312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47044, d320312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47044, d320312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d47045 q = 1) (hb : d320313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47045, d320313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d47045, d320313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d47047 q = 1) (hb : d320315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86270 q ha hb
    | true =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86245 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d320244 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d320316 q = 1) (hb : d321687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320316, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d320316, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d47053 q = 1) (hb : d320318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86271 q ha hb
    | true =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d47054 q = 1) (hb : d320319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d320320 q = 1) (hb : d321688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320320, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d320320, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d320321 q = 1) (hb : d321689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320321, d321689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d320321, d321689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d320322 q = 1) (hb : d321690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320322, d321690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d320322, d321690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d320323 q = 1) (hb : d321691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320323, d321691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320323, d321691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro86273 (p : Pattern) (ha : d320343 p = 1) (hb : d321698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47047 q = 1) (hb : d320315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86270 q ha hb
    | true =>
      simp only [d47047, d320315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86245 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320316 q = 1) (hb : d321687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320316, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320316, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d47053 q = 1) (hb : d320318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86271 q ha hb
    | true =>
      simp only [d47053, d320318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47054 q = 1) (hb : d320319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47054, d320319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320320 q = 1) (hb : d321688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320320, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320320, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d320341 q = 1) (hb : d321696 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320341, d321696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320341, d321696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320342 q = 1) (hb : d321697 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320342, d321697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320342, d321697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320343 q = 1) (hb : d321698 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320343, d321698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320343, d321698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro86274 (p : Pattern) (ha : d47091 p = 1) (hb : d320356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d320351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d320352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d320353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d320354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47090 q = 1) (hb : d320355 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47091 q = 1) (hb : d320356 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47091, d320356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47091, d320356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86275 (p : Pattern) (ha : d47112 p = 1) (hb : d320377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47092 q = 1) (hb : d320357 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47092, d320357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47092, d320357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86274 q ha hb
  have h2 (q : Pattern) (ha : d47093 q = 1) (hb : d320358 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47093, d320358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47093, d320358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47094 q = 1) (hb : d320359 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47094, d320359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47094, d320359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47097 q = 1) (hb : d320362 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86274 q ha hb
    | true =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
  have h5 (q : Pattern) (ha : d47098 q = 1) (hb : d320363 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47099 q = 1) (hb : d320364 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47100 q = 1) (hb : d320365 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47100, d320365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47100, d320365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47107 q = 1) (hb : d320372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86252 q ha hb
  have h9 (q : Pattern) (ha : d47108 q = 1) (hb : d320373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47109 q = 1) (hb : d320374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47110 q = 1) (hb : d320375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d47111 q = 1) (hb : d320376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47111, d320376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47111, d320376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47112 q = 1) (hb : d320377 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47112, d320377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47112, d320377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro86276 (p : Pattern) (ha : d47117 p = 1) (hb : d320382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47097 q = 1) (hb : d320362 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86274 q ha hb
    | true =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
  have h2 (q : Pattern) (ha : d47098 q = 1) (hb : d320363 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47099 q = 1) (hb : d320364 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47107 q = 1) (hb : d320372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86252 q ha hb
  have h5 (q : Pattern) (ha : d47108 q = 1) (hb : d320373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47109 q = 1) (hb : d320374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47110 q = 1) (hb : d320375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47115 q = 1) (hb : d320380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47115, d320380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47116 q = 1) (hb : d320381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47116, d320381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47116, d320381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47117 q = 1) (hb : d320382 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47117, d320382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d47117, d320382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro86277 (p : Pattern) (ha : d47123 p = 1) (hb : d320388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47113 q = 1) (hb : d320378 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47113, d320378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86275 q ha hb
    | true =>
      simp only [d47113, d320378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47114 q = 1) (hb : d320379 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47114, d320379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47114, d320379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47118 q = 1) (hb : d320383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86276 q ha hb
    | true =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47119 q = 1) (hb : d320384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47120 q = 1) (hb : d320385 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47120, d320385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47120, d320385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47121 q = 1) (hb : d320386 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47121, d320386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47121, d320386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47122 q = 1) (hb : d320387 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47122, d320387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47122, d320387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47123 q = 1) (hb : d320388 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47123, d320388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47123, d320388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86278 (p : Pattern) (ha : d47131 p = 1) (hb : d320396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47118 q = 1) (hb : d320383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86276 q ha hb
    | true =>
      simp only [d47118, d320383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47119 q = 1) (hb : d320384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47119, d320384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47126 q = 1) (hb : d320391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86253 q ha hb
    | true =>
      simp only [d47126, d320391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47127 q = 1) (hb : d320392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47127, d320392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47128 q = 1) (hb : d320393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47128, d320393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47128, d320393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47129 q = 1) (hb : d320394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47129, d320394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47129, d320394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47130 q = 1) (hb : d320395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47130, d320395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47130, d320395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47131 q = 1) (hb : d320396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47131, d320396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47131, d320396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86279 (p : Pattern) (ha : d47193 p = 1) (hb : d320424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d320351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d320352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d320353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d320354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47090 q = 1) (hb : d320355 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47090, d320355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47193 q = 1) (hb : d320424 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47193, d320424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47193, d320424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86280 (p : Pattern) (ha : d47199 p = 1) (hb : d320430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47097 q = 1) (hb : d320362 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86274 q ha hb
    | true =>
      simp only [d47097, d320362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
  have h2 (q : Pattern) (ha : d47098 q = 1) (hb : d320363 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d320363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47099 q = 1) (hb : d320364 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d320364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47107 q = 1) (hb : d320372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q ha hb
    | true =>
      simp only [d47107, d320372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86252 q ha hb
  have h5 (q : Pattern) (ha : d47108 q = 1) (hb : d320373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d320373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47109 q = 1) (hb : d320374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d320374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47110 q = 1) (hb : d320375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47110, d320375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47194 q = 1) (hb : d320425 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47194, d320425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86279 q ha hb
    | true =>
      simp only [d47194, d320425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d47195 q = 1) (hb : d320426 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47195, d320426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47195, d320426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47196 q = 1) (hb : d320427 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47196, d320427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47196, d320427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47197 q = 1) (hb : d320428 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47197, d320428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47197, d320428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47198 q = 1) (hb : d320429 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47198, d320429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47198, d320429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47199 q = 1) (hb : d320430 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47199, d320430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47199, d320430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro86281 (p : Pattern) (ha : d47205 p = 1) (hb : d320436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47200 q = 1) (hb : d320431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47200, d320431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86280 q ha hb
    | true =>
      simp only [d47200, d320431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47201 q = 1) (hb : d320432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47201, d320432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47201, d320432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47202 q = 1) (hb : d320433 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47202, d320433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47202, d320433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47203 q = 1) (hb : d320434 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47203, d320434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47203, d320434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47204 q = 1) (hb : d320435 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47204, d320435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47204, d320435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47205 q = 1) (hb : d320436 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47205, d320436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47205, d320436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86282 (p : Pattern) (ha : d320442 p = 1) (hb : d321708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47132 q = 1) (hb : d320397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47132, d320397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86277 q ha hb
    | true =>
      simp only [d47132, d320397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86278 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320423 q = 1) (hb : d321704 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320423, d321704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320423, d321704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d47206 q = 1) (hb : d320437 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47206, d320437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86281 q ha hb
    | true =>
      simp only [d47206, d320437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47207 q = 1) (hb : d320438 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47207, d320438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47207, d320438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320439 q = 1) (hb : d321705 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320439, d321705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320439, d321705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d320440 q = 1) (hb : d321706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320440, d321706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320440, d321706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320441 q = 1) (hb : d321707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320441, d321707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320441, d321707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320442 q = 1) (hb : d321708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320442, d321708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320442, d321708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro86283 (p : Pattern) (ha : d320459 p = 1) (hb : d321714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46922 q = 1) (hb : d320240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46922, d320240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46922, d320240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86244 q ha hb
  have h2 (q : Pattern) (ha : d46923 q = 1) (hb : d320241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46923, d320241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46923, d320241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46932 q = 1) (hb : d320250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d320250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86244 q ha hb
    | true =>
      simp only [d46932, d320250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86247 q ha hb
  have h4 (q : Pattern) (ha : d46933 q = 1) (hb : d320251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d320251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46933, d320251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46934 q = 1) (hb : d320252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46934, d320252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46934, d320252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320324 q = 1) (hb : d321692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320324, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86265 q ha hb
    | true =>
      simp only [d320324, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86272 q ha hb
  have h7 (q : Pattern) (ha : d47072 q = 1) (hb : d320337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47072, d320337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86248 q ha hb
    | true =>
      simp only [d47072, d320337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86249 q ha hb
  have h8 (q : Pattern) (ha : d320338 q = 1) (hb : d321693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320338, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320338, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d320339 q = 1) (hb : d321694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320339, d321694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320339, d321694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d320340 q = 1) (hb : d321695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320340, d321695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d320340, d321695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320344 q = 1) (hb : d321699 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320344, d321699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320344, d321699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86273 q ha hb
  have h12 (q : Pattern) (ha : d47081 q = 1) (hb : d320346 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47081, d320346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47081, d320346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86250 q ha hb
  have h13 (q : Pattern) (ha : d320347 q = 1) (hb : d321700 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320347, d321700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320347, d321700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d320348 q = 1) (hb : d321701 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320348, d321701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320348, d321701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d320349 q = 1) (hb : d321702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320349, d321702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d320349, d321702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d320350 q = 1) (hb : d321703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320350, d321703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320350, d321703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320443 q = 1) (hb : d321709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320443, d321709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320443, d321709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86282 q ha hb
  have h18 (q : Pattern) (ha : d47223 q = 1) (hb : d320454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d47223, d320454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47223, d320454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86255 q ha hb
  have h19 (q : Pattern) (ha : d320455 q = 1) (hb : d321710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320455, d321710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320455, d321710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d320456 q = 1) (hb : d321711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320456, d321711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d320456, d321711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d320457 q = 1) (hb : d321712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320457, d321712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d320457, d321712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d320458 q = 1) (hb : d321713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320458, d321713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d320458, d321713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d320459 q = 1) (hb : d321714 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d320459, d321714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320459, d321714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro86284 (p : Pattern) (ha : d320465 p = 1) (hb : d321720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320460 q = 1) (hb : d321715 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d320460, d321715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320460, d321715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86283 q ha hb
  have h2 (q : Pattern) (ha : d320461 q = 1) (hb : d321716 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d320461, d321716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320461, d321716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320462 q = 1) (hb : d321717 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d320462, d321717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320462, d321717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320463 q = 1) (hb : d321718 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d320463, d321718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320463, d321718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320464 q = 1) (hb : d321719 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d320464, d321719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320464, d321719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320465 q = 1) (hb : d321720 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d320465, d321720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320465, d321720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86285 (p : Pattern) (ha : d320471 p = 1) (hb : d321726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d320987 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d320987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86013 q ha hb
    | true =>
      simp only [d319211, d320987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86059 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d321266 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d321266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d321266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86113 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d321267 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d321267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d321267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d321636 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d321636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d321636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86175 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d321637 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d321637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d321637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d321638 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d321638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d321638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86233 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d321681 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d321681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d321681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320466 q = 1) (hb : d321721 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320466, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320466, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86284 q ha hb
  have h12 (q : Pattern) (ha : d320467 q = 1) (hb : d321722 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320467, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320467, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320468 q = 1) (hb : d321723 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320468, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320468, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320469 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320469, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320469, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320470 q = 1) (hb : d321725 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d321725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d321725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320471 q = 1) (hb : d321726 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d321726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320471, d321726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro86286 (p : Pattern) (ha : d320477 p = 1) (hb : d321732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d321727 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d321727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86285 q ha hb
    | true =>
      simp only [d320472, d321727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d321728 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d321728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d321728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d321729 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d321729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d321729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d321730 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d321730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d321730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d321731 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d321731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d321731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d321732 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d321732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d321732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86287 (p : Pattern) (ha : d320483 p = 1) (hb : d321738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d321733 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d321733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86286 q ha hb
    | true =>
      simp only [d320478, d321733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d321734 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d321734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d321734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d321735 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d321735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d321735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d321736 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d321736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d321736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d321737 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d321737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d321737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d321738 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d321738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d321738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86288 (p : Pattern) (ha : d320489 p = 1) (hb : d321744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d321739 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d321739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86287 q ha hb
    | true =>
      simp only [d320484, d321739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d321740 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d321740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d321740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d321741 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d321741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d321741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d321742 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d321742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d321742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d321743 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d321743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d321743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d321744 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d321744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d321744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86289 (p : Pattern) (ha : d320495 p = 1) (hb : d321750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d321745 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d321745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86288 q ha hb
    | true =>
      simp only [d320490, d321745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d321746 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d321746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d321746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d321747 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d321747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d321747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d321748 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d321748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d321748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d321749 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d321749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d321749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d321750 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d321750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d321750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86290 (p : Pattern) (ha : d320501 p = 1) (hb : d321756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d321751 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d321751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86289 q ha hb
    | true =>
      simp only [d320496, d321751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d321752 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d321752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d321752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d321753 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d321753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d321753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d321754 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d321754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d321754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d321755 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d321755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d321755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d321756 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d321756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d321756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86291 (p : Pattern) (ha : d320507 p = 1) (hb : d321762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d321757 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d321757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86290 q ha hb
    | true =>
      simp only [d320502, d321757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d321758 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d321758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d321758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d321759 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d321759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d321759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d321760 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d321760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d321760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d321761 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d321761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d321761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d321762 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d321762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d321762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86292 (p : Pattern) (ha : d320513 p = 1) (hb : d321768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d321763 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d321763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86291 q ha hb
    | true =>
      simp only [d320508, d321763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d321764 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d321764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d321764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d321765 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d321765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d321765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d321766 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d321766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d321766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d321767 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d321767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d321767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d321768 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d321768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d321768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86293 (p : Pattern) (ha : d312377 p = 1) (hb : d318725 p = 1) : d321771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33246 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85614 q ha hb
    | true =>
      simp only [d33246, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33306 q = 1) (hb : d318725 q = 1) : d320606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33307 q = 1) (hb : d318725 q = 1) : d320607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33307, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33308 q = 1) (hb : d318725 q = 1) : d320608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33309 q = 1) (hb : d318725 q = 1) : d320609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d312377 q = 1) (hb : d318725 q = 1) : d321771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312377, d321771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312377, d321771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86294 (p : Pattern) (ha : d312387 p = 1) (hb : d318725 p = 1) : d321781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d318725 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33282 q = 1) (hb : d318725 q = 1) : d320582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85619 q ha hb
    | true =>
      simp only [d33282, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312383 q = 1) (hb : d318725 q = 1) : d321777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312383, d321777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312383, d321777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312384 q = 1) (hb : d318725 q = 1) : d321778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312384, d321778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312384, d321778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312385 q = 1) (hb : d318725 q = 1) : d321779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312385, d321779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312385, d321779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312386 q = 1) (hb : d318725 q = 1) : d321780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312386, d321780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312386, d321780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d312387 q = 1) (hb : d318725 q = 1) : d321781 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312387, d321781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312387, d321781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86295 (p : Pattern) (ha : d312393 p = 1) (hb : d318725 p = 1) : d321787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33311 q = 1) (hb : d318725 q = 1) : d320611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85622 q ha hb
    | true =>
      simp only [d33311, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85623 q ha hb
  have h2 (q : Pattern) (ha : d33312 q = 1) (hb : d318725 q = 1) : d320612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33312, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312375 q = 1) (hb : d318725 q = 1) : d321769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312375, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312375, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312376 q = 1) (hb : d318725 q = 1) : d321770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312376, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312376, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312378 q = 1) (hb : d318725 q = 1) : d321772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312378, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312378, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86293 q ha hb
  have h6 (q : Pattern) (ha : d312379 q = 1) (hb : d318725 q = 1) : d321773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312379, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312379, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312380 q = 1) (hb : d318725 q = 1) : d321774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312380, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312380, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312381 q = 1) (hb : d318725 q = 1) : d321775 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312381, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312381, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d312382 q = 1) (hb : d318725 q = 1) : d321776 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312382, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312382, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312388 q = 1) (hb : d318725 q = 1) : d321782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312388, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312388, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86294 q ha hb
  have h11 (q : Pattern) (ha : d312389 q = 1) (hb : d318725 q = 1) : d321783 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312389, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312389, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312390 q = 1) (hb : d318725 q = 1) : d321784 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312390, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312390, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312391 q = 1) (hb : d318725 q = 1) : d321785 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312391, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312391, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d312392 q = 1) (hb : d318725 q = 1) : d321786 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312392, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312392, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312393 q = 1) (hb : d318725 q = 1) : d321787 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312393, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312393, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86296 (p : Pattern) (ha : d312399 p = 1) (hb : d318725 p = 1) : d321793 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d318725 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d312394 q = 1) (hb : d318725 q = 1) : d321788 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312394, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312394, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86295 q ha hb
  have h3 (q : Pattern) (ha : d312395 q = 1) (hb : d318725 q = 1) : d321789 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312395, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312395, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312396 q = 1) (hb : d318725 q = 1) : d321790 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312396, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312396, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312397 q = 1) (hb : d318725 q = 1) : d321791 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312397, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312397, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312398 q = 1) (hb : d318725 q = 1) : d321792 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312398, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312398, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d312399 q = 1) (hb : d318725 q = 1) : d321793 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312399, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312399, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86297 (p : Pattern) (ha : d312402 p = 1) (hb : d318725 p = 1) : d321796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33527 q = 1) (hb : d318725 q = 1) : d320778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33527, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85653 q ha hb
    | true =>
      simp only [d33527, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85654 q ha hb
  have h2 (q : Pattern) (ha : d33528 q = 1) (hb : d318725 q = 1) : d320779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33528, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33528, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33529 q = 1) (hb : d318725 q = 1) : d320780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33529, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33529, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33530 q = 1) (hb : d318725 q = 1) : d320781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33530, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33530, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33531 q = 1) (hb : d318725 q = 1) : d320782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33531, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33531, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312402 q = 1) (hb : d318725 q = 1) : d321796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312402, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312402, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86298 (p : Pattern) (ha : d312413 p = 1) (hb : d318725 p = 1) : d321807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312408 q = 1) (hb : d318725 q = 1) : d321802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312408, d321802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85690 q ha hb
    | true =>
      simp only [d312408, d321802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85660 q ha hb
  have h2 (q : Pattern) (ha : d312409 q = 1) (hb : d318725 q = 1) : d321803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312409, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312409, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312410 q = 1) (hb : d318725 q = 1) : d321804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312410, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312410, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312411 q = 1) (hb : d318725 q = 1) : d321805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312411, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312411, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312412 q = 1) (hb : d318725 q = 1) : d321806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312412, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312412, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312413 q = 1) (hb : d318725 q = 1) : d321807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312413, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312413, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86299 (p : Pattern) (ha : d312419 p = 1) (hb : d318725 p = 1) : d321813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33533 q = 1) (hb : d318725 q = 1) : d320784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33533, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85652 q ha hb
    | true =>
      simp only [d33533, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85655 q ha hb
  have h2 (q : Pattern) (ha : d33534 q = 1) (hb : d318725 q = 1) : d320785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33534, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33534, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312400 q = 1) (hb : d318725 q = 1) : d321794 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312400, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312400, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312401 q = 1) (hb : d318725 q = 1) : d321795 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312401, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312401, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312403 q = 1) (hb : d318725 q = 1) : d321797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312403, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312403, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86297 q ha hb
  have h6 (q : Pattern) (ha : d312404 q = 1) (hb : d318725 q = 1) : d321798 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312404, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312404, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312405 q = 1) (hb : d318725 q = 1) : d321799 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312405, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312405, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312406 q = 1) (hb : d318725 q = 1) : d321800 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312406, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312406, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d312407 q = 1) (hb : d318725 q = 1) : d321801 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312407, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312407, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312414 q = 1) (hb : d318725 q = 1) : d321808 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312414, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312414, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86298 q ha hb
  have h11 (q : Pattern) (ha : d312415 q = 1) (hb : d318725 q = 1) : d321809 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312415, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312415, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312416 q = 1) (hb : d318725 q = 1) : d321810 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312416, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312416, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312417 q = 1) (hb : d318725 q = 1) : d321811 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312417, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312417, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d312418 q = 1) (hb : d318725 q = 1) : d321812 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312418, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312418, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312419 q = 1) (hb : d318725 q = 1) : d321813 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312419, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312419, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86300 (p : Pattern) (ha : d312425 p = 1) (hb : d318725 p = 1) : d321819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312420 q = 1) (hb : d318725 q = 1) : d321814 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312420, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312420, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86299 q ha hb
  have h2 (q : Pattern) (ha : d312421 q = 1) (hb : d318725 q = 1) : d321815 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312421, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312421, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312422 q = 1) (hb : d318725 q = 1) : d321816 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312422, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312422, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312423 q = 1) (hb : d318725 q = 1) : d321817 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312423, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312423, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312424 q = 1) (hb : d318725 q = 1) : d321818 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312424, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312424, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312425 q = 1) (hb : d318725 q = 1) : d321819 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312425, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312425, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86301 (p : Pattern) (ha : d312429 p = 1) (hb : d318725 p = 1) : d321823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33867 q = 1) (hb : d318725 q = 1) : d321033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33867, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85704 q ha hb
    | true =>
      simp only [d33867, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85705 q ha hb
  have h2 (q : Pattern) (ha : d33868 q = 1) (hb : d318725 q = 1) : d321034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33868, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33868, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33869 q = 1) (hb : d318725 q = 1) : d321035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33869, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33869, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33870 q = 1) (hb : d318725 q = 1) : d321036 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33870, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33870, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33871 q = 1) (hb : d318725 q = 1) : d321037 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33871, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33871, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312429 q = 1) (hb : d318725 q = 1) : d321823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312429, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312429, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86302 (p : Pattern) (ha : d312440 p = 1) (hb : d318725 p = 1) : d321834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312435 q = 1) (hb : d318725 q = 1) : d321829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312435, d321829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85745 q ha hb
    | true =>
      simp only [d312435, d321829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85713 q ha hb
  have h2 (q : Pattern) (ha : d312436 q = 1) (hb : d318725 q = 1) : d321830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312436, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312436, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312437 q = 1) (hb : d318725 q = 1) : d321831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312437, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312437, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312438 q = 1) (hb : d318725 q = 1) : d321832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312438, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312438, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312439 q = 1) (hb : d318725 q = 1) : d321833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312439, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312439, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312440 q = 1) (hb : d318725 q = 1) : d321834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312440, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312440, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86303 (p : Pattern) (ha : d312446 p = 1) (hb : d318725 p = 1) : d321840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33873 q = 1) (hb : d318725 q = 1) : d321039 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33873, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85703 q ha hb
    | true =>
      simp only [d33873, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85706 q ha hb
  have h2 (q : Pattern) (ha : d33874 q = 1) (hb : d318725 q = 1) : d321040 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33874, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33874, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312427 q = 1) (hb : d318725 q = 1) : d321821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312427, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312427, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312428 q = 1) (hb : d318725 q = 1) : d321822 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312428, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312428, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312430 q = 1) (hb : d318725 q = 1) : d321824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312430, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312430, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86301 q ha hb
  have h6 (q : Pattern) (ha : d312431 q = 1) (hb : d318725 q = 1) : d321825 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312431, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312431, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312432 q = 1) (hb : d318725 q = 1) : d321826 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312432, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312432, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312433 q = 1) (hb : d318725 q = 1) : d321827 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312433, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312433, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d312434 q = 1) (hb : d318725 q = 1) : d321828 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312434, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312434, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312441 q = 1) (hb : d318725 q = 1) : d321835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312441, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312441, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86302 q ha hb
  have h11 (q : Pattern) (ha : d312442 q = 1) (hb : d318725 q = 1) : d321836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312442, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312442, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312443 q = 1) (hb : d318725 q = 1) : d321837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312443, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312443, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312444 q = 1) (hb : d318725 q = 1) : d321838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312444, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312444, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d312445 q = 1) (hb : d318725 q = 1) : d321839 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312445, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312445, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312446 q = 1) (hb : d318725 q = 1) : d321840 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312446, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312446, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86304 (p : Pattern) (ha : d312452 p = 1) (hb : d318725 p = 1) : d321846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312447 q = 1) (hb : d318725 q = 1) : d321841 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312447, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312447, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86303 q ha hb
  have h2 (q : Pattern) (ha : d312448 q = 1) (hb : d318725 q = 1) : d321842 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312448, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312448, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312449 q = 1) (hb : d318725 q = 1) : d321843 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312449, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312449, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312450 q = 1) (hb : d318725 q = 1) : d321844 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312450, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312450, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312451 q = 1) (hb : d318725 q = 1) : d321845 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312451, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312451, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312452 q = 1) (hb : d318725 q = 1) : d321846 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312452, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312452, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86305 (p : Pattern) (ha : d312457 p = 1) (hb : d318725 p = 1) : d321851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34326 q = 1) (hb : d318725 q = 1) : d321366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34326, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85764 q ha hb
    | true =>
      simp only [d34326, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85765 q ha hb
  have h2 (q : Pattern) (ha : d34327 q = 1) (hb : d318725 q = 1) : d321367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34327, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34327, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34328 q = 1) (hb : d318725 q = 1) : d321368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34328, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34328, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34329 q = 1) (hb : d318725 q = 1) : d321369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34329, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34329, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34330 q = 1) (hb : d318725 q = 1) : d321370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34330, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34330, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312457 q = 1) (hb : d318725 q = 1) : d321851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312457, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312457, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86306 (p : Pattern) (ha : d312468 p = 1) (hb : d318725 p = 1) : d321862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312463 q = 1) (hb : d318725 q = 1) : d321857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312463, d321857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85807 q ha hb
    | true =>
      simp only [d312463, d321857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85773 q ha hb
  have h2 (q : Pattern) (ha : d312464 q = 1) (hb : d318725 q = 1) : d321858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312464, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312464, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312465 q = 1) (hb : d318725 q = 1) : d321859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312465, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312465, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312466 q = 1) (hb : d318725 q = 1) : d321860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312466, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312466, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312467 q = 1) (hb : d318725 q = 1) : d321861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312467, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312467, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312468 q = 1) (hb : d318725 q = 1) : d321862 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312468, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312468, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86307 (p : Pattern) (ha : d312474 p = 1) (hb : d318725 p = 1) : d321868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34332 q = 1) (hb : d318725 q = 1) : d321372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34332, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85763 q ha hb
    | true =>
      simp only [d34332, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85766 q ha hb
  have h2 (q : Pattern) (ha : d34333 q = 1) (hb : d318725 q = 1) : d321373 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34333, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34333, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312455 q = 1) (hb : d318725 q = 1) : d321849 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312455, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312455, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312456 q = 1) (hb : d318725 q = 1) : d321850 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312456, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312456, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312458 q = 1) (hb : d318725 q = 1) : d321852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312458, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312458, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86305 q ha hb
  have h6 (q : Pattern) (ha : d312459 q = 1) (hb : d318725 q = 1) : d321853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312459, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312459, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312460 q = 1) (hb : d318725 q = 1) : d321854 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312460, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312460, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312461 q = 1) (hb : d318725 q = 1) : d321855 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312461, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312461, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d312462 q = 1) (hb : d318725 q = 1) : d321856 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312462, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312462, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312469 q = 1) (hb : d318725 q = 1) : d321863 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312469, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312469, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86306 q ha hb
  have h11 (q : Pattern) (ha : d312470 q = 1) (hb : d318725 q = 1) : d321864 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312470, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312470, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312471 q = 1) (hb : d318725 q = 1) : d321865 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312471, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312471, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312472 q = 1) (hb : d318725 q = 1) : d321866 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312472, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312472, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d312473 q = 1) (hb : d318725 q = 1) : d321867 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312473, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312473, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312474 q = 1) (hb : d318725 q = 1) : d321868 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312474, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312474, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86308 (p : Pattern) (ha : d312480 p = 1) (hb : d318725 p = 1) : d321874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312475 q = 1) (hb : d318725 q = 1) : d321869 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312475, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312475, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86307 q ha hb
  have h2 (q : Pattern) (ha : d312476 q = 1) (hb : d318725 q = 1) : d321870 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312476, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312476, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312477 q = 1) (hb : d318725 q = 1) : d321871 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312477, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312477, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312478 q = 1) (hb : d318725 q = 1) : d321872 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312478, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312478, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312479 q = 1) (hb : d318725 q = 1) : d321873 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312479, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312479, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312480 q = 1) (hb : d318725 q = 1) : d321874 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312480, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312480, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86309 (p : Pattern) (ha : d312486 p = 1) (hb : d318725 p = 1) : d321880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34892 q = 1) (hb : d318725 q = 1) : d46532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34892, d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85836 q ha hb
    | true =>
      simp only [d34892, d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85837 q ha hb
  have h2 (q : Pattern) (ha : d34893 q = 1) (hb : d318725 q = 1) : d46533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34893, d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34893, d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34894 q = 1) (hb : d318725 q = 1) : d46534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34894, d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34894, d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34895 q = 1) (hb : d318725 q = 1) : d46535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34895, d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34895, d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34896 q = 1) (hb : d318725 q = 1) : d46536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34896, d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34896, d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312486 q = 1) (hb : d318725 q = 1) : d321880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312486, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312486, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86310 (p : Pattern) (ha : d312497 p = 1) (hb : d318725 p = 1) : d321891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312492 q = 1) (hb : d318725 q = 1) : d321886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312492, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85881 q ha hb
    | true =>
      simp only [d312492, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85845 q ha hb
  have h2 (q : Pattern) (ha : d312493 q = 1) (hb : d318725 q = 1) : d321887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312493, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312493, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312494 q = 1) (hb : d318725 q = 1) : d321888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312494, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312494, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312495 q = 1) (hb : d318725 q = 1) : d321889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312495, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312495, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312496 q = 1) (hb : d318725 q = 1) : d321890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312496, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312496, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312497 q = 1) (hb : d318725 q = 1) : d321891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312497, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312497, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86311 (p : Pattern) (ha : d312503 p = 1) (hb : d318725 p = 1) : d321897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34898 q = 1) (hb : d318725 q = 1) : d46538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34898, d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85835 q ha hb
    | true =>
      simp only [d34898, d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85838 q ha hb
  have h2 (q : Pattern) (ha : d34899 q = 1) (hb : d318725 q = 1) : d46539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34899, d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34899, d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312484 q = 1) (hb : d318725 q = 1) : d321878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312484, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312484, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312485 q = 1) (hb : d318725 q = 1) : d321879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312485, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312485, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312487 q = 1) (hb : d318725 q = 1) : d321881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312487, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312487, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86309 q ha hb
  have h6 (q : Pattern) (ha : d312488 q = 1) (hb : d318725 q = 1) : d321882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312488, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312488, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312489 q = 1) (hb : d318725 q = 1) : d321883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312489, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312489, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312490 q = 1) (hb : d318725 q = 1) : d321884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312490, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312490, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d312491 q = 1) (hb : d318725 q = 1) : d321885 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312491, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312491, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312498 q = 1) (hb : d318725 q = 1) : d321892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312498, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312498, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86310 q ha hb
  have h11 (q : Pattern) (ha : d312499 q = 1) (hb : d318725 q = 1) : d321893 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312499, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312499, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312500 q = 1) (hb : d318725 q = 1) : d321894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312500, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312500, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312501 q = 1) (hb : d318725 q = 1) : d321895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312501, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312501, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d312502 q = 1) (hb : d318725 q = 1) : d321896 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312502, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312502, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312503 q = 1) (hb : d318725 q = 1) : d321897 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312503, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312503, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86312 (p : Pattern) (ha : d312509 p = 1) (hb : d318725 p = 1) : d321903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312504 q = 1) (hb : d318725 q = 1) : d321898 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312504, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312504, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86311 q ha hb
  have h2 (q : Pattern) (ha : d312505 q = 1) (hb : d318725 q = 1) : d321899 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312505, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312505, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312506 q = 1) (hb : d318725 q = 1) : d321900 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312506, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312506, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312507 q = 1) (hb : d318725 q = 1) : d321901 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312507, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312507, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312508 q = 1) (hb : d318725 q = 1) : d321902 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312508, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312508, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312509 q = 1) (hb : d318725 q = 1) : d321903 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312509, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312509, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86313 (p : Pattern) (ha : d312516 p = 1) (hb : d318725 p = 1) : d321910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35475 q = 1) (hb : d318725 q = 1) : d46926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d35475, d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85914 q ha hb
    | true =>
      simp only [d35475, d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85915 q ha hb
  have h2 (q : Pattern) (ha : d35476 q = 1) (hb : d318725 q = 1) : d46927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d35476, d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35476, d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35477 q = 1) (hb : d318725 q = 1) : d46928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d35477, d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35477, d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35478 q = 1) (hb : d318725 q = 1) : d46929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d35478, d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35478, d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35479 q = 1) (hb : d318725 q = 1) : d46930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d35479, d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35479, d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312516 q = 1) (hb : d318725 q = 1) : d321910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312516, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312516, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86314 (p : Pattern) (ha : d312523 p = 1) (hb : d318725 p = 1) : d47117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35771 q = 1) (hb : d318725 q = 1) : d47097 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35771, d47097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85952 q ha hb
    | true =>
      simp only [d35771, d47097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85922 q ha hb
  have h2 (q : Pattern) (ha : d35772 q = 1) (hb : d318725 q = 1) : d47098 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35772, d47098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35772, d47098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35773 q = 1) (hb : d318725 q = 1) : d47099 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35773, d47099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35773, d47099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35780 q = 1) (hb : d318725 q = 1) : d47107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35780, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85922 q ha hb
    | true =>
      simp only [d35780, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85954 q ha hb
  have h5 (q : Pattern) (ha : d35781 q = 1) (hb : d318725 q = 1) : d47108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35781, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35781, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35782 q = 1) (hb : d318725 q = 1) : d47109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35782, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35782, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d35783 q = 1) (hb : d318725 q = 1) : d47110 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35783, d47110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35783, d47110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d35799 q = 1) (hb : d318725 q = 1) : d47107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35799, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85922 q ha hb
    | true =>
      simp only [d35799, d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85923 q ha hb
  have h9 (q : Pattern) (ha : d35800 q = 1) (hb : d318725 q = 1) : d47108 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35800, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35800, d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d35801 q = 1) (hb : d318725 q = 1) : d47109 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35801, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35801, d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d35802 q = 1) (hb : d318725 q = 1) : d47115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35802, d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d35802, d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312522 q = 1) (hb : d318725 q = 1) : d47116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312522, d47116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312522, d47116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d312523 q = 1) (hb : d318725 q = 1) : d47117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312523, d47117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312523, d47117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro86315 (p : Pattern) (ha : d312529 p = 1) (hb : d318725 p = 1) : d47131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312524 q = 1) (hb : d318725 q = 1) : d47118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312524, d47118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86314 q ha hb
    | true =>
      simp only [d312524, d47118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312525 q = 1) (hb : d318725 q = 1) : d47119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312525, d47119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312525, d47119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35805 q = 1) (hb : d318725 q = 1) : d47126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d35805, d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85924 q ha hb
    | true =>
      simp only [d35805, d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35806 q = 1) (hb : d318725 q = 1) : d47127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d35806, d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35806, d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312526 q = 1) (hb : d318725 q = 1) : d47128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312526, d47128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312526, d47128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312527 q = 1) (hb : d318725 q = 1) : d47129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312527, d47129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312527, d47129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312528 q = 1) (hb : d318725 q = 1) : d47130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312528, d47130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312528, d47130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312529 q = 1) (hb : d318725 q = 1) : d47131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312529, d47131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312529, d47131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86316 (p : Pattern) (ha : d312535 p = 1) (hb : d318725 p = 1) : d321921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2058 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85895 q ha hb
  have h2 (q : Pattern) (ha : d258695 q = 1) (hb : d318725 q = 1) : d258695 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d312530 q = 1) (hb : d318725 q = 1) : d321916 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d312530, d321916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312530, d321916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85896 q ha hb
  have h4 (q : Pattern) (ha : d312531 q = 1) (hb : d318725 q = 1) : d321917 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d312531, d321917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312531, d321917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312532 q = 1) (hb : d318725 q = 1) : d321918 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d312532, d321918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312532, d321918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10405 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85895 q ha hb
    | true =>
      simp only [d10405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10406 q = 1) (hb : d318725 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85896 q ha hb
    | true =>
      simp only [d10406, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10407 q = 1) (hb : d318725 q = 1) : d46872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10407, d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10408 q = 1) (hb : d318725 q = 1) : d46873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10408, d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d312533 q = 1) (hb : d318725 q = 1) : d321919 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d312533, d321919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312533, d321919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d312534 q = 1) (hb : d318725 q = 1) : d321920 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d312534, d321920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312534, d321920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312535 q = 1) (hb : d318725 q = 1) : d321921 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d312535, d321921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312535, d321921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro86317 (p : Pattern) (ha : d312541 p = 1) (hb : d318725 p = 1) : d321927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35765 q = 1) (hb : d318725 q = 1) : d47086 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35765, d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35765, d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85903 q ha hb
  have h2 (q : Pattern) (ha : d35417 q = 1) (hb : d318725 q = 1) : d46877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35417, d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85903 q ha hb
    | true =>
      simp only [d35417, d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35766 q = 1) (hb : d318725 q = 1) : d47087 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35766, d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35766, d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35418 q = 1) (hb : d318725 q = 1) : d46878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35418, d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35418, d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35767 q = 1) (hb : d318725 q = 1) : d47088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d35767, d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35767, d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35768 q = 1) (hb : d318725 q = 1) : d47089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d35768, d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35768, d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d35797 q = 1) (hb : d318725 q = 1) : d47095 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d35797, d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d35797, d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d318725 q = 1) : d47101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85905 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d318725 q = 1) : d46889 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85905 q ha hb
    | true =>
      simp only [d10412, d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d318725 q = 1) : d47102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d312536 q = 1) (hb : d318725 q = 1) : d321922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d312536, d321922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86316 q ha hb
    | true =>
      simp only [d312536, d321922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312537 q = 1) (hb : d318725 q = 1) : d321923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d312537, d321923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312537, d321923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312538 q = 1) (hb : d318725 q = 1) : d321924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d312538, d321924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312538, d321924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d312539 q = 1) (hb : d318725 q = 1) : d321925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d312539, d321925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312539, d321925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312540 q = 1) (hb : d318725 q = 1) : d321926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d312540, d321926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d312540, d321926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d312541 q = 1) (hb : d318725 q = 1) : d321927 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d312541, d321927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312541, d321927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro86318 (p : Pattern) (ha : d312547 p = 1) (hb : d318725 p = 1) : d321933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312542 q = 1) (hb : d318725 q = 1) : d321928 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d312542, d321928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85922 q ha hb
    | true =>
      simp only [d312542, d321928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86317 q ha hb
  have h2 (q : Pattern) (ha : d312543 q = 1) (hb : d318725 q = 1) : d321929 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d312543, d321929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312543, d321929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312544 q = 1) (hb : d318725 q = 1) : d321930 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d312544, d321930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312544, d321930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312545 q = 1) (hb : d318725 q = 1) : d321931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d312545, d321931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312545, d321931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312546 q = 1) (hb : d318725 q = 1) : d321932 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312546, d321932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312546, d321932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312547 q = 1) (hb : d318725 q = 1) : d321933 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312547, d321933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312547, d321933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86319 (p : Pattern) (ha : d312553 p = 1) (hb : d318725 p = 1) : d321939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312548 q = 1) (hb : d318725 q = 1) : d321934 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312548, d321934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86318 q ha hb
    | true =>
      simp only [d312548, d321934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312549 q = 1) (hb : d318725 q = 1) : d321935 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312549, d321935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312549, d321935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312550 q = 1) (hb : d318725 q = 1) : d321936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312550, d321936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312550, d321936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312551 q = 1) (hb : d318725 q = 1) : d321937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312551, d321937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312551, d321937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312552 q = 1) (hb : d318725 q = 1) : d321938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312552, d321938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312552, d321938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312553 q = 1) (hb : d318725 q = 1) : d321939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312553, d321939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312553, d321939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86320 (p : Pattern) (ha : d312559 p = 1) (hb : d318725 p = 1) : d321945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312554 q = 1) (hb : d318725 q = 1) : d321940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312554, d321940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86315 q ha hb
    | true =>
      simp only [d312554, d321940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86319 q ha hb
  have h2 (q : Pattern) (ha : d312555 q = 1) (hb : d318725 q = 1) : d321941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312555, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312555, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312556 q = 1) (hb : d318725 q = 1) : d321942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312556, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312556, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312557 q = 1) (hb : d318725 q = 1) : d321943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312557, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312557, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312558 q = 1) (hb : d318725 q = 1) : d321944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312558, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312558, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312559 q = 1) (hb : d318725 q = 1) : d321945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312559, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312559, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86321 (p : Pattern) (ha : d312565 p = 1) (hb : d318725 p = 1) : d321951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35481 q = 1) (hb : d318725 q = 1) : d46932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d35481, d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85913 q ha hb
    | true =>
      simp only [d35481, d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85916 q ha hb
  have h2 (q : Pattern) (ha : d35482 q = 1) (hb : d318725 q = 1) : d46933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d35482, d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35482, d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312514 q = 1) (hb : d318725 q = 1) : d321908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312514, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312514, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312515 q = 1) (hb : d318725 q = 1) : d321909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312515, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312515, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312517 q = 1) (hb : d318725 q = 1) : d321911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312517, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312517, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86313 q ha hb
  have h6 (q : Pattern) (ha : d312518 q = 1) (hb : d318725 q = 1) : d321912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312518, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312518, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d312519 q = 1) (hb : d318725 q = 1) : d321913 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312519, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312519, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d312520 q = 1) (hb : d318725 q = 1) : d321914 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312520, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312520, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d312521 q = 1) (hb : d318725 q = 1) : d321915 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312521, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312521, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312560 q = 1) (hb : d318725 q = 1) : d321946 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312560, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312560, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86320 q ha hb
  have h11 (q : Pattern) (ha : d312561 q = 1) (hb : d318725 q = 1) : d321947 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312561, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312561, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d312562 q = 1) (hb : d318725 q = 1) : d321948 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312562, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312562, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d312563 q = 1) (hb : d318725 q = 1) : d321949 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312563, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312563, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d312564 q = 1) (hb : d318725 q = 1) : d321950 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312564, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312564, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d312565 q = 1) (hb : d318725 q = 1) : d321951 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312565, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312565, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro86322 (p : Pattern) (ha : d312571 p = 1) (hb : d318725 p = 1) : d321957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312566 q = 1) (hb : d318725 q = 1) : d321952 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312566, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312566, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86321 q ha hb
  have h2 (q : Pattern) (ha : d312567 q = 1) (hb : d318725 q = 1) : d321953 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312567, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312567, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d312568 q = 1) (hb : d318725 q = 1) : d321954 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312568, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312568, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312569 q = 1) (hb : d318725 q = 1) : d321955 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312569, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312569, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d312570 q = 1) (hb : d318725 q = 1) : d321956 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312570, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312570, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312571 q = 1) (hb : d318725 q = 1) : d321957 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312571, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312571, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86323 (p : Pattern) (ha : d312577 p = 1) (hb : d318725 p = 1) : d321963 p = 1 := by
  have h0 (q : Pattern) (ha : d312426 q = 1) (hb : d318725 q = 1) : d321820 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312426, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86296 q ha hb
    | true =>
      simp only [d312426, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86300 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d312453 q = 1) (hb : d318725 q = 1) : d321847 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312453, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312453, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86304 q ha hb
  have h3 (q : Pattern) (ha : d312454 q = 1) (hb : d318725 q = 1) : d321848 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312454, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312454, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d312481 q = 1) (hb : d318725 q = 1) : d321875 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312481, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312481, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86308 q ha hb
  have h5 (q : Pattern) (ha : d312482 q = 1) (hb : d318725 q = 1) : d321876 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312482, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312482, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d312483 q = 1) (hb : d318725 q = 1) : d321877 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312483, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312483, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d312510 q = 1) (hb : d318725 q = 1) : d321904 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312510, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312510, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86312 q ha hb
  have h8 (q : Pattern) (ha : d312511 q = 1) (hb : d318725 q = 1) : d321905 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312511, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312511, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d312512 q = 1) (hb : d318725 q = 1) : d321906 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312512, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312512, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d312513 q = 1) (hb : d318725 q = 1) : d321907 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312513, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312513, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d312572 q = 1) (hb : d318725 q = 1) : d321958 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312572, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312572, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86322 q ha hb
  have h12 (q : Pattern) (ha : d312573 q = 1) (hb : d318725 q = 1) : d321959 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312573, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312573, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d312574 q = 1) (hb : d318725 q = 1) : d321960 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312574, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312574, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d312575 q = 1) (hb : d318725 q = 1) : d321961 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312575, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312575, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d312576 q = 1) (hb : d318725 q = 1) : d321962 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d312576, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312576, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d312577 q = 1) (hb : d318725 q = 1) : d321963 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d312577, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d312577, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro86324 (p : Pattern) (ha : d312583 p = 1) (hb : d318725 p = 1) : d321969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312578 q = 1) (hb : d318725 q = 1) : d321964 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d312578, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86323 q ha hb
    | true =>
      simp only [d312578, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312579 q = 1) (hb : d318725 q = 1) : d321965 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d312579, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312579, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312580 q = 1) (hb : d318725 q = 1) : d321966 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d312580, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312580, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312581 q = 1) (hb : d318725 q = 1) : d321967 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d312581, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312581, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312582 q = 1) (hb : d318725 q = 1) : d321968 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d312582, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312582, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312583 q = 1) (hb : d318725 q = 1) : d321969 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d312583, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312583, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86325 (p : Pattern) (ha : d312589 p = 1) (hb : d318725 p = 1) : d321975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312584 q = 1) (hb : d318725 q = 1) : d321970 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d312584, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86324 q ha hb
    | true =>
      simp only [d312584, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312585 q = 1) (hb : d318725 q = 1) : d321971 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d312585, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312585, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312586 q = 1) (hb : d318725 q = 1) : d321972 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d312586, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312586, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312587 q = 1) (hb : d318725 q = 1) : d321973 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d312587, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312587, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312588 q = 1) (hb : d318725 q = 1) : d321974 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d312588, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312588, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312589 q = 1) (hb : d318725 q = 1) : d321975 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d312589, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312589, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86326 (p : Pattern) (ha : d312595 p = 1) (hb : d318725 p = 1) : d321981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312590 q = 1) (hb : d318725 q = 1) : d321976 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d312590, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86325 q ha hb
    | true =>
      simp only [d312590, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312591 q = 1) (hb : d318725 q = 1) : d321977 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d312591, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312591, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312592 q = 1) (hb : d318725 q = 1) : d321978 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d312592, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312592, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312593 q = 1) (hb : d318725 q = 1) : d321979 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d312593, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312593, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312594 q = 1) (hb : d318725 q = 1) : d321980 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d312594, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312594, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312595 q = 1) (hb : d318725 q = 1) : d321981 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d312595, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312595, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86327 (p : Pattern) (ha : d312601 p = 1) (hb : d318725 p = 1) : d321987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312596 q = 1) (hb : d318725 q = 1) : d321982 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d312596, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86326 q ha hb
    | true =>
      simp only [d312596, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312597 q = 1) (hb : d318725 q = 1) : d321983 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d312597, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312597, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312598 q = 1) (hb : d318725 q = 1) : d321984 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d312598, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312598, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312599 q = 1) (hb : d318725 q = 1) : d321985 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d312599, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312599, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312600 q = 1) (hb : d318725 q = 1) : d321986 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d312600, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312600, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312601 q = 1) (hb : d318725 q = 1) : d321987 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d312601, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312601, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86328 (p : Pattern) (ha : d312607 p = 1) (hb : d318725 p = 1) : d321993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312602 q = 1) (hb : d318725 q = 1) : d321988 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d312602, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86327 q ha hb
    | true =>
      simp only [d312602, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312603 q = 1) (hb : d318725 q = 1) : d321989 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d312603, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312603, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312604 q = 1) (hb : d318725 q = 1) : d321990 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d312604, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312604, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312605 q = 1) (hb : d318725 q = 1) : d321991 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d312605, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312605, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312606 q = 1) (hb : d318725 q = 1) : d321992 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d312606, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312606, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312607 q = 1) (hb : d318725 q = 1) : d321993 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d312607, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312607, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86329 (p : Pattern) (ha : d312613 p = 1) (hb : d318725 p = 1) : d321999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312608 q = 1) (hb : d318725 q = 1) : d321994 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d312608, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86328 q ha hb
    | true =>
      simp only [d312608, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312609 q = 1) (hb : d318725 q = 1) : d321995 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d312609, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312609, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312610 q = 1) (hb : d318725 q = 1) : d321996 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d312610, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312610, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312611 q = 1) (hb : d318725 q = 1) : d321997 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d312611, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312611, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312612 q = 1) (hb : d318725 q = 1) : d321998 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d312612, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312612, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312613 q = 1) (hb : d318725 q = 1) : d321999 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d312613, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312613, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86330 (p : Pattern) (ha : d312619 p = 1) (hb : d318725 p = 1) : d322005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d312614 q = 1) (hb : d318725 q = 1) : d322000 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d312614, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86329 q ha hb
    | true =>
      simp only [d312614, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d312615 q = 1) (hb : d318725 q = 1) : d322001 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d312615, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312615, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d312616 q = 1) (hb : d318725 q = 1) : d322002 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d312616, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312616, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d312617 q = 1) (hb : d318725 q = 1) : d322003 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d312617, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312617, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d312618 q = 1) (hb : d318725 q = 1) : d322004 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d312618, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312618, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d312619 q = 1) (hb : d318725 q = 1) : d322005 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d312619, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312619, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86331 (p : Pattern) (ha : d104 p = 1) (hb : d318759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d318755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d318755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d318755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d318756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d318756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d318756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d318757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d318757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d318757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d318758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d318758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d318758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d318759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d318759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d318759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86332 (p : Pattern) (ha : d111 p = 1) (hb : d318766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d318755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d318755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d318755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d318756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d318756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d318756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d318757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d318757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d318757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d318758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d318758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d318758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d318762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d318762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d318762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d318763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d318763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d318763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d318764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d318764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d318764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d318765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d318765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d318765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d318766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d318766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d318766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86333 (p : Pattern) (ha : d406 p = 1) (hb : d318773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d318762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d318762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d318762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d318763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d318763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d318763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d318771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d318771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d318771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d318772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d318772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d318772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d318773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d318773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d318773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86334 (p : Pattern) (ha : d462 p = 1) (hb : d318802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318797 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d318798 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d318798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d318798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d318799 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d318799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d318799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d318800 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d318800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d318800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d318801 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d318801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d318801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d318802 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d318802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d318802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86335 (p : Pattern) (ha : d53647 p = 1) (hb : d318808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d318767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d318767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86331 q ha hb
    | true =>
      simp only [d112, d318767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86332 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d318768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d318768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d318768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d318769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d318769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d318769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d318770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d318770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d318770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d318774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d318774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d318774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86333 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d318775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d318775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d318775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d318776 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d318776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d318776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d318777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d318777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d318777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d318778 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d318778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d318778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d318803 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d318803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d318803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86334 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d318804 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d318804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d318804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d318805 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d318805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d318805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d318806 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d318806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d318806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d318807 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d318807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d318807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d318808 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d318808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d318808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro86336 (p : Pattern) (ha : d318887 p = 1) (hb : d320603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d318754 q = 1) (hb : d320539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318754, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85978 q ha hb
    | true =>
      simp only [d318754, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d318877 q = 1) (hb : d320599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318877, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d318877, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d318884 q = 1) (hb : d320600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318884, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318884, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d318885 q = 1) (hb : d320601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318885, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d318885, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318886 q = 1) (hb : d320602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318886, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318886, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318887 q = 1) (hb : d320603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318887, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318887, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86337 (p : Pattern) (ha : d318906 p = 1) (hb : d320610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318754 q = 1) (hb : d320539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318754, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85978 q ha hb
    | true =>
      simp only [d318754, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d318877 q = 1) (hb : d320599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318877, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d318877, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d318884 q = 1) (hb : d320600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318884, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318884, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d318885 q = 1) (hb : d320601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318885, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318885, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318886 q = 1) (hb : d320602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318886, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318886, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318892 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d318896 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d318761 q = 1) (hb : d320546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318761, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85980 q ha hb
    | true =>
      simp only [d318761, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d318899 q = 1) (hb : d320606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318899, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d318899, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318903 q = 1) (hb : d320607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318903, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318903, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d318904 q = 1) (hb : d320608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318904, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d318904, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d318905 q = 1) (hb : d320609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318905, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d318905, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d318906 q = 1) (hb : d320610 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318906, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318906, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86338 (p : Pattern) (ha : d318915 p = 1) (hb : d321771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318761 q = 1) (hb : d320546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318761, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85980 q ha hb
    | true =>
      simp only [d318761, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d318899 q = 1) (hb : d320606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318899, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318899, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318903 q = 1) (hb : d320607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318903, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318903, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318913 q = 1) (hb : d320608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318913, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318913, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318914 q = 1) (hb : d320609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318914, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318914, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318915 q = 1) (hb : d321771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318915, d321771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318915, d321771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86339 (p : Pattern) (ha : d318955 p = 1) (hb : d321781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318797 q = 1) (hb : d320582 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318797, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85985 q ha hb
    | true =>
      simp only [d318797, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d318945 q = 1) (hb : d321777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318945, d321777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318945, d321777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318951 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318952 q = 1) (hb : d321778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318952, d321778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318952, d321778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318953 q = 1) (hb : d321779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318953, d321779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318953, d321779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318954 q = 1) (hb : d321780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318954, d321780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318954, d321780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318955 q = 1) (hb : d321781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318955, d321781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318955, d321781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86340 (p : Pattern) (ha : d318961 p = 1) (hb : d321787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318828 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318907 q = 1) (hb : d320611 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318907, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86336 q ha hb
    | true =>
      simp only [d318907, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86337 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318910 q = 1) (hb : d320612 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318910, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318910, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318911 q = 1) (hb : d321769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318911, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318911, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318912 q = 1) (hb : d321770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318912, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318912, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318916 q = 1) (hb : d321772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318916, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318916, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86338 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d318917 q = 1) (hb : d321773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318917, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318917, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d318918 q = 1) (hb : d321774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318918, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318918, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d318919 q = 1) (hb : d321775 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318919, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318919, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d318920 q = 1) (hb : d321776 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318920, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318920, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318956 q = 1) (hb : d321782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318956, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318956, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86339 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318957 q = 1) (hb : d321783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318957, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318957, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d318958 q = 1) (hb : d321784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318958, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318958, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d318959 q = 1) (hb : d321785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318959, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318959, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d318960 q = 1) (hb : d321786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318960, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318960, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d318961 q = 1) (hb : d321787 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318961, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318961, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86341 (p : Pattern) (ha : d318967 p = 1) (hb : d321793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d318809 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86335 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d318810 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d318811 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d318812 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d318813 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318962 q = 1) (hb : d321788 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318962, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318962, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86340 q ha hb
  have h8 (q : Pattern) (ha : d318963 q = 1) (hb : d321789 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318963, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318963, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318964 q = 1) (hb : d321790 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318964, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318964, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318965 q = 1) (hb : d321791 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318965, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318965, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318966 q = 1) (hb : d321792 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318966, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318966, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318967 q = 1) (hb : d321793 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318967, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d318967, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro86342 (p : Pattern) (ha : d319082 p = 1) (hb : d320773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d318985 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318985, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86016 q ha hb
    | true =>
      simp only [d318985, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86017 q ha hb
  have h5 (q : Pattern) (ha : d319072 q = 1) (hb : d320769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319072, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319072, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d319079 q = 1) (hb : d320770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319079, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319079, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d319080 q = 1) (hb : d320771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319080, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319080, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319081 q = 1) (hb : d320772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319081, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319081, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319082 q = 1) (hb : d320773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319082, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319082, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86343 (p : Pattern) (ha : d319103 p = 1) (hb : d320783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318985 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318985, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86016 q ha hb
    | true =>
      simp only [d318985, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86017 q ha hb
  have h4 (q : Pattern) (ha : d319072 q = 1) (hb : d320769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319072, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319072, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d319079 q = 1) (hb : d320770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319079, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319079, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319080 q = 1) (hb : d320771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319080, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319080, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319081 q = 1) (hb : d320772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319081, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319081, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319088 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319093 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d318995 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318995, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86019 q ha hb
    | true =>
      simp only [d318995, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86020 q ha hb
  have h13 (q : Pattern) (ha : d319096 q = 1) (hb : d320779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319096, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319096, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319100 q = 1) (hb : d320780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319100, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319100, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319101 q = 1) (hb : d320781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319101, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d319101, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319102 q = 1) (hb : d320782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319102, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d319102, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319103 q = 1) (hb : d320783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319103, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319103, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86344 (p : Pattern) (ha : d319123 p = 1) (hb : d321796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318995 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d318995, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86019 q ha hb
    | true =>
      simp only [d318995, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86020 q ha hb
  have h3 (q : Pattern) (ha : d319096 q = 1) (hb : d320779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319096, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319096, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319100 q = 1) (hb : d320780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319100, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319100, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319121 q = 1) (hb : d320781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319121, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319121, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319122 q = 1) (hb : d320782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319122, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319122, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319123 q = 1) (hb : d321796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319123, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319123, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86345 (p : Pattern) (ha : d319191 p = 1) (hb : d321807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319180 q = 1) (hb : d321802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319180, d321802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86053 q ha hb
    | true =>
      simp only [d319180, d321802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86056 q ha hb
  have h3 (q : Pattern) (ha : d319181 q = 1) (hb : d321803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319181, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319181, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319188 q = 1) (hb : d321804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319188, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319188, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319189 q = 1) (hb : d321805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319189, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319189, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319190 q = 1) (hb : d321806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319190, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319190, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319191 q = 1) (hb : d321807 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319191, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319191, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86346 (p : Pattern) (ha : d319204 p = 1) (hb : d321813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319003 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319104 q = 1) (hb : d320784 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319104, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86342 q ha hb
    | true =>
      simp only [d319104, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86343 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319118 q = 1) (hb : d320785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319118, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319118, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319119 q = 1) (hb : d321794 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319119, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319119, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319120 q = 1) (hb : d321795 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319120, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319120, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319124 q = 1) (hb : d321797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319124, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319124, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86344 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319126 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319127 q = 1) (hb : d321798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319127, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319127, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319128 q = 1) (hb : d321799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319128, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319128, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319129 q = 1) (hb : d321800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319129, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319129, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319130 q = 1) (hb : d321801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319130, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319130, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319192 q = 1) (hb : d321808 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319192, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319192, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86345 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319200 q = 1) (hb : d321809 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319200, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319200, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319201 q = 1) (hb : d321810 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319201, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319201, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319202 q = 1) (hb : d321811 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319202, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319202, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319203 q = 1) (hb : d321812 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319203, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319203, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319204 q = 1) (hb : d321813 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319204, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319204, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86347 (p : Pattern) (ha : d319210 p = 1) (hb : d321819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319205 q = 1) (hb : d321814 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319205, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319205, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86346 q ha hb
  have h2 (q : Pattern) (ha : d319206 q = 1) (hb : d321815 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319206, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319206, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319207 q = 1) (hb : d321816 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319207, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319207, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319208 q = 1) (hb : d321817 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319208, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319208, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319209 q = 1) (hb : d321818 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319209, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319209, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319210 q = 1) (hb : d321819 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319210, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319210, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86348 (p : Pattern) (ha : d319354 p = 1) (hb : d321028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d319247 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319247, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86066 q ha hb
    | true =>
      simp only [d319247, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86067 q ha hb
  have h5 (q : Pattern) (ha : d319344 q = 1) (hb : d321024 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319344, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319344, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d319351 q = 1) (hb : d321025 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319351, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319351, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d319352 q = 1) (hb : d321026 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319352, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319352, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319353 q = 1) (hb : d321027 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319353, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319353, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319354 q = 1) (hb : d321028 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319354, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319354, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86349 (p : Pattern) (ha : d319375 p = 1) (hb : d321038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319247 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319247, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86066 q ha hb
    | true =>
      simp only [d319247, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86067 q ha hb
  have h4 (q : Pattern) (ha : d319344 q = 1) (hb : d321024 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319344, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319344, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d319351 q = 1) (hb : d321025 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319351, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319351, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319352 q = 1) (hb : d321026 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319352, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319352, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319353 q = 1) (hb : d321027 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319353, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319353, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319360 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319365 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d319257 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319257, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86069 q ha hb
    | true =>
      simp only [d319257, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86070 q ha hb
  have h13 (q : Pattern) (ha : d319368 q = 1) (hb : d321034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319368, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319368, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319372 q = 1) (hb : d321035 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319372, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319372, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319373 q = 1) (hb : d321036 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319373, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d319373, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319374 q = 1) (hb : d321037 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319374, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d319374, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319375 q = 1) (hb : d321038 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319375, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319375, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86350 (p : Pattern) (ha : d319395 p = 1) (hb : d321823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319257 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319257, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86069 q ha hb
    | true =>
      simp only [d319257, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86070 q ha hb
  have h3 (q : Pattern) (ha : d319368 q = 1) (hb : d321034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319368, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319368, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319372 q = 1) (hb : d321035 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319372, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319372, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319393 q = 1) (hb : d321036 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319393, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319393, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319394 q = 1) (hb : d321037 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319394, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319394, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319395 q = 1) (hb : d321823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319395, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319395, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86351 (p : Pattern) (ha : d319480 p = 1) (hb : d321834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319469 q = 1) (hb : d321829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319469, d321829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86107 q ha hb
    | true =>
      simp only [d319469, d321829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86110 q ha hb
  have h3 (q : Pattern) (ha : d319470 q = 1) (hb : d321830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319470, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319470, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319477 q = 1) (hb : d321831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319477, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319477, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319478 q = 1) (hb : d321832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319478, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319478, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319479 q = 1) (hb : d321833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319479, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319479, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319480 q = 1) (hb : d321834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319480, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319480, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86352 (p : Pattern) (ha : d319493 p = 1) (hb : d321840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319376 q = 1) (hb : d321039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319376, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86348 q ha hb
    | true =>
      simp only [d319376, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86349 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319390 q = 1) (hb : d321040 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319390, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319390, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319391 q = 1) (hb : d321821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319391, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319391, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319392 q = 1) (hb : d321822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319392, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319392, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319396 q = 1) (hb : d321824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319396, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319396, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86350 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319398 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319399 q = 1) (hb : d321825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319399, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319399, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319400 q = 1) (hb : d321826 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319400, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319400, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319401 q = 1) (hb : d321827 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319401, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319401, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319402 q = 1) (hb : d321828 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319402, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319402, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319481 q = 1) (hb : d321835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319481, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319481, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86351 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319489 q = 1) (hb : d321836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319489, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319489, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319490 q = 1) (hb : d321837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319490, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319490, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319491 q = 1) (hb : d321838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319491, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319491, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319492 q = 1) (hb : d321839 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319492, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319492, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319493 q = 1) (hb : d321840 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319493, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319493, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86353 (p : Pattern) (ha : d319499 p = 1) (hb : d321846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319494 q = 1) (hb : d321841 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319494, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319494, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86352 q ha hb
  have h2 (q : Pattern) (ha : d319495 q = 1) (hb : d321842 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319495, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319495, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319496 q = 1) (hb : d321843 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319496, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319496, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319497 q = 1) (hb : d321844 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319497, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319497, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319498 q = 1) (hb : d321845 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319498, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319498, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319499 q = 1) (hb : d321846 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319499, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319499, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86354 (p : Pattern) (ha : d319705 p = 1) (hb : d321361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d319593 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86125 q ha hb
    | true =>
      simp only [d319593, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86126 q ha hb
  have h5 (q : Pattern) (ha : d319686 q = 1) (hb : d321357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319686, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d319702 q = 1) (hb : d321358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d319702, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d319703 q = 1) (hb : d321359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319703, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319704 q = 1) (hb : d321360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319704, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d319705 q = 1) (hb : d321361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319705, d321361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319705, d321361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86355 (p : Pattern) (ha : d319726 p = 1) (hb : d321371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319593 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319593, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86125 q ha hb
    | true =>
      simp only [d319593, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86126 q ha hb
  have h4 (q : Pattern) (ha : d319686 q = 1) (hb : d321357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d319686, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d319702 q = 1) (hb : d321358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d319702, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319703 q = 1) (hb : d321359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319703, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319704 q = 1) (hb : d321360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319704, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319711 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319716 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d319603 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319603, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86128 q ha hb
    | true =>
      simp only [d319603, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86129 q ha hb
  have h13 (q : Pattern) (ha : d319719 q = 1) (hb : d321367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d319719, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319723 q = 1) (hb : d321368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319723, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319724 q = 1) (hb : d321369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319724, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d319724, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319725 q = 1) (hb : d321370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319725, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d319725, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d319726 q = 1) (hb : d321371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319726, d321371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319726, d321371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86356 (p : Pattern) (ha : d319746 p = 1) (hb : d321851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319603 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319603, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86128 q ha hb
    | true =>
      simp only [d319603, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86129 q ha hb
  have h3 (q : Pattern) (ha : d319719 q = 1) (hb : d321367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319719, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319723 q = 1) (hb : d321368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319723, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319744 q = 1) (hb : d321369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319744, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319744, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319745 q = 1) (hb : d321370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319745, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319745, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319746 q = 1) (hb : d321851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319746, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319746, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86357 (p : Pattern) (ha : d319867 p = 1) (hb : d321862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319847 q = 1) (hb : d321857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319847, d321857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86167 q ha hb
    | true =>
      simp only [d319847, d321857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86172 q ha hb
  have h3 (q : Pattern) (ha : d319848 q = 1) (hb : d321858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319848, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319848, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319863 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319864 q = 1) (hb : d321859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319864, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319864, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319865 q = 1) (hb : d321860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319865, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319865, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319866 q = 1) (hb : d321861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319866, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319866, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319867 q = 1) (hb : d321862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319867, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319867, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86358 (p : Pattern) (ha : d319880 p = 1) (hb : d321868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319727 q = 1) (hb : d321372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319727, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86354 q ha hb
    | true =>
      simp only [d319727, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86355 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319740 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319741 q = 1) (hb : d321373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319741, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d319741, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319742 q = 1) (hb : d321849 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319742, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319742, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319743 q = 1) (hb : d321850 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319743, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319743, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319747 q = 1) (hb : d321852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319747, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319747, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86356 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319749 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319750 q = 1) (hb : d321853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319750, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319750, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319751 q = 1) (hb : d321854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319751, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319751, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319752 q = 1) (hb : d321855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319752, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319752, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319753 q = 1) (hb : d321856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319753, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319753, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319868 q = 1) (hb : d321863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319868, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319868, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86357 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319875 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319876 q = 1) (hb : d321864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319876, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319876, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319877 q = 1) (hb : d321865 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319877, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319877, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319878 q = 1) (hb : d321866 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319878, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319878, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319879 q = 1) (hb : d321867 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319879, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319879, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319880 q = 1) (hb : d321868 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319880, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319880, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86359 (p : Pattern) (ha : d319886 p = 1) (hb : d321874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319881 q = 1) (hb : d321869 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319881, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319881, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86358 q ha hb
  have h2 (q : Pattern) (ha : d319882 q = 1) (hb : d321870 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319882, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319882, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319883 q = 1) (hb : d321871 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319883, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319883, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319884 q = 1) (hb : d321872 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319884, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319884, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319885 q = 1) (hb : d321873 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319885, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319885, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319886 q = 1) (hb : d321874 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319886, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319886, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86360 (p : Pattern) (ha : d46527 p = 1) (hb : d320029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319979 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46522 q = 1) (hb : d319953 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86186 q ha hb
    | true =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86187 q ha hb
  have h5 (q : Pattern) (ha : d46523 q = 1) (hb : d320003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d320003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46523, d320003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d320025 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46524 q = 1) (hb : d320026 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d320026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46524, d320026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46525 q = 1) (hb : d320027 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d320027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46525, d320027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46526 q = 1) (hb : d320028 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d320028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46526, d320028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46527 q = 1) (hb : d320029 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d320029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d320029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86361 (p : Pattern) (ha : d46537 p = 1) (hb : d320050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319979 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46522 q = 1) (hb : d319953 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86186 q ha hb
    | true =>
      simp only [d46522, d319953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86187 q ha hb
  have h4 (q : Pattern) (ha : d46523 q = 1) (hb : d320003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d320003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46523, d320003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d320025 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46524 q = 1) (hb : d320026 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d320026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46524, d320026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46525 q = 1) (hb : d320027 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d320027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46525, d320027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46526 q = 1) (hb : d320028 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d320028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d320028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d320035 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d320040 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d320042 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46532 q = 1) (hb : d319963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d319963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86189 q ha hb
    | true =>
      simp only [d46532, d319963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86190 q ha hb
  have h13 (q : Pattern) (ha : d46533 q = 1) (hb : d320043 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d320043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46533, d320043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320046 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46534 q = 1) (hb : d320047 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d320047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46534, d320047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46535 q = 1) (hb : d320048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d320048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46535, d320048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46536 q = 1) (hb : d320049 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d320049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46536, d320049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46537 q = 1) (hb : d320050 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d320050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46537, d320050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86362 (p : Pattern) (ha : d320070 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46532 q = 1) (hb : d319963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d319963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86189 q ha hb
    | true =>
      simp only [d46532, d319963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86190 q ha hb
  have h3 (q : Pattern) (ha : d46533 q = 1) (hb : d320043 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d320043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46533, d320043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46534 q = 1) (hb : d320047 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d320047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46534, d320047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46535 q = 1) (hb : d320068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d320068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d320068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46536 q = 1) (hb : d320069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d320069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d320069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320070 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320070, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320070, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro86363 (p : Pattern) (ha : d320161 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d320135 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320135, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86226 q hb ha
    | true =>
      simp only [d320135, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86198 q hb ha
  have h3 (q : Pattern) (ha : d320136 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320136, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320136, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320158 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320158, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320158, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320159 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320159, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320159, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320160 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320160, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320160, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320161 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320161, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320161, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86364 (p : Pattern) (ha : d320174 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d320051 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d320051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86360 q ha hb
    | true =>
      simp only [d46538, d320051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86361 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320064 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46539 q = 1) (hb : d320065 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d320065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d320065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320066 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320066, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d320066, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320067 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320067, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320067, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320071 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320071, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320071, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86362 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d320073 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d320074 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320074, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320074, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d320075 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320075, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320075, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d320076 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320076, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320076, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d320077 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320077, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320077, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320162 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320162, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320162, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86363 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320170 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320170, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320170, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d320171 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320171, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320171, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d320172 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320172, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320172, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d320173 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320173, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320173, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d320174 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d320174, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320174, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86365 (p : Pattern) (ha : d320180 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320175 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d320175, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320175, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86364 q ha hb
  have h2 (q : Pattern) (ha : d320176 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d320176, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320176, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320177 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d320177, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320177, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320178 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d320178, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320178, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320179 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d320179, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320179, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320180 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d320180, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320180, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86366 (p : Pattern) (ha : d46921 p = 1) (hb : d320302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320282 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46916 q = 1) (hb : d320234 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86242 q ha hb
    | true =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86243 q ha hb
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d320283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d320283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d320283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d320298 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d320299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d320299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d320299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d320300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d320300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d320300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d320301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d320301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d320301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d320302 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d320302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d320302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86367 (p : Pattern) (ha : d46931 p = 1) (hb : d320323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d320260 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46916 q = 1) (hb : d320234 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86242 q ha hb
    | true =>
      simp only [d46916, d320234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86243 q ha hb
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d320283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d320283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d320283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d320298 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d320299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d320299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d320299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d320300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d320300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d320300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d320301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d320301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d320301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d320308 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d320313 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d320315 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46926 q = 1) (hb : d320244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d320244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86245 q ha hb
    | true =>
      simp only [d46926, d320244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86246 q ha hb
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d320316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d320316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d320316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320319 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d320320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d320320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d320320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d320321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d320321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d320321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d320322 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d320322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d320322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d320323 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d320323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d320323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86368 (p : Pattern) (ha : d320343 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46926 q = 1) (hb : d320244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d320244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86245 q ha hb
    | true =>
      simp only [d46926, d320244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86246 q ha hb
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d320316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d320316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d320316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320319 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d320320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d320320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d320320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d320341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d320341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d320341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d320342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d320342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d320342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320343 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320343, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320343, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro86369 (p : Pattern) (ha : d320403 p = 1) (hb : d321921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320398 q = 1) (hb : d321916 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d320398, d321916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro82485 q hb ha
    | true =>
      simp only [d320398, d321916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86234 q hb ha
  have h2 (q : Pattern) (ha : d320399 q = 1) (hb : d321917 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d320399, d321917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320399, d321917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320400 q = 1) (hb : d321918 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d320400, d321918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320400, d321918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46871 q = 1) (hb : d320189 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86234 q ha hb
    | true =>
      simp only [d46871, d320189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46872 q = 1) (hb : d320190 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46872, d320190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46873 q = 1) (hb : d320191 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, d320191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d320401 q = 1) (hb : d321919 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d320401, d321919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320401, d321919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d320402 q = 1) (hb : d321920 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d320402, d321920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320402, d321920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d320403 q = 1) (hb : d321921 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d320403, d321921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320403, d321921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro86370 (p : Pattern) (ha : d320409 p = 1) (hb : d321927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d320351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d320351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d320195 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86235 q ha hb
    | true =>
      simp only [d46877, d320195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d320352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d320352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d320196 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d320196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d320353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d320353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d320354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d320354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d320360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d320360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d320366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d320366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86238 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d320207 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86238 q ha hb
    | true =>
      simp only [d46889, d320207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d320367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d320367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320404 q = 1) (hb : d321922 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d320404, d321922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86369 q ha hb
    | true =>
      simp only [d320404, d321922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d320405 q = 1) (hb : d321923 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320405, d321923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320405, d321923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d320406 q = 1) (hb : d321924 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d320406, d321924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d320406, d321924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320407 q = 1) (hb : d321925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d320407, d321925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320407, d321925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d320408 q = 1) (hb : d321926 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d320408, d321926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d320408, d321926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d320409 q = 1) (hb : d321927 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d320409, d321927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d320409, d321927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro86371 (p : Pattern) (ha : d320415 p = 1) (hb : d321933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320410 q = 1) (hb : d321928 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d320410, d321928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86251 q hb ha
    | true =>
      simp only [d320410, d321928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86370 q ha hb
  have h2 (q : Pattern) (ha : d320411 q = 1) (hb : d321929 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d320411, d321929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320411, d321929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320412 q = 1) (hb : d321930 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d320412, d321930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320412, d321930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320413 q = 1) (hb : d321931 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d320413, d321931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320413, d321931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320414 q = 1) (hb : d321932 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d320414, d321932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320414, d321932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320415 q = 1) (hb : d321933 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d320415, d321933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320415, d321933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86372 (p : Pattern) (ha : d320421 p = 1) (hb : d321939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320416 q = 1) (hb : d321934 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d320416, d321934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86371 q ha hb
    | true =>
      simp only [d320416, d321934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320417 q = 1) (hb : d321935 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d320417, d321935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320417, d321935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320418 q = 1) (hb : d321936 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d320418, d321936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320418, d321936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320419 q = 1) (hb : d321937 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d320419, d321937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320419, d321937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320420 q = 1) (hb : d321938 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d320420, d321938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320420, d321938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320421 q = 1) (hb : d321939 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d320421, d321939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320421, d321939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86373 (p : Pattern) (ha : d320442 p = 1) (hb : d321945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d320422 q = 1) (hb : d321940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d320422, d321940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86278 q hb ha
    | true =>
      simp only [d320422, d321940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86372 q ha hb
  have h3 (q : Pattern) (ha : d320423 q = 1) (hb : d321941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320423, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320423, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320439 q = 1) (hb : d321942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320439, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320439, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320440 q = 1) (hb : d321943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320440, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320440, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320441 q = 1) (hb : d321944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320441, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320441, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320442 q = 1) (hb : d321945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320442, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320442, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86374 (p : Pattern) (ha : d320459 p = 1) (hb : d321951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d320252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d320324 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d320324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86366 q ha hb
    | true =>
      simp only [d46932, d320324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86367 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d320338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d320338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d320338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320339 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320339, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d320339, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d320340 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320340, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320340, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320344 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320344, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320344, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86368 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d320346 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d320347 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320347, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d320347, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d320348 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320348, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320348, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d320349 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320349, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320349, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d320350 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320350, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320350, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320443 q = 1) (hb : d321946 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320443, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d320443, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86373 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d320454 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320455 q = 1) (hb : d321947 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320455, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320455, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d320456 q = 1) (hb : d321948 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d320456, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320456, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d320457 q = 1) (hb : d321949 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d320457, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d320457, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d320458 q = 1) (hb : d321950 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d320458, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d320458, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d320459 q = 1) (hb : d321951 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d320459, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d320459, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86375 (p : Pattern) (ha : d320465 p = 1) (hb : d321957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320460 q = 1) (hb : d321952 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d320460, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320460, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86374 q ha hb
  have h2 (q : Pattern) (ha : d320461 q = 1) (hb : d321953 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d320461, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320461, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320462 q = 1) (hb : d321954 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d320462, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320462, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320463 q = 1) (hb : d321955 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d320463, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320463, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320464 q = 1) (hb : d321956 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d320464, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320464, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320465 q = 1) (hb : d321957 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d320465, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d320465, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86376 (p : Pattern) (ha : d320471 p = 1) (hb : d321963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d321820 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86341 q ha hb
    | true =>
      simp only [d319211, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86347 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d321847 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86353 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d321848 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d321875 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86359 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d321876 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d321877 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86365 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d321907 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320466 q = 1) (hb : d321958 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320466, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320466, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86375 q ha hb
  have h12 (q : Pattern) (ha : d320467 q = 1) (hb : d321959 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320467, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320467, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320468 q = 1) (hb : d321960 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320468, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320468, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320469 q = 1) (hb : d321961 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320469, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320469, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320470 q = 1) (hb : d321962 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320471 q = 1) (hb : d321963 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320471, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro86377 (p : Pattern) (ha : d320477 p = 1) (hb : d321969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d321964 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86376 q ha hb
    | true =>
      simp only [d320472, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d321965 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d321966 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d321967 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d321968 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d321969 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86378 (p : Pattern) (ha : d320483 p = 1) (hb : d321975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d321970 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86377 q ha hb
    | true =>
      simp only [d320478, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d321971 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d321972 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d321973 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d321974 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d321975 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86379 (p : Pattern) (ha : d320489 p = 1) (hb : d321981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d321976 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86378 q ha hb
    | true =>
      simp only [d320484, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d321977 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d321978 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d321979 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d321980 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d321981 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86380 (p : Pattern) (ha : d320495 p = 1) (hb : d321987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d321982 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86379 q ha hb
    | true =>
      simp only [d320490, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d321983 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d321984 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d321985 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d321986 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d321987 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86381 (p : Pattern) (ha : d320501 p = 1) (hb : d321993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d321988 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86380 q ha hb
    | true =>
      simp only [d320496, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d321989 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d321990 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d321991 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d321992 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d321993 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86382 (p : Pattern) (ha : d320507 p = 1) (hb : d321999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d321994 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86381 q ha hb
    | true =>
      simp only [d320502, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d321995 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d321996 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d321997 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d321998 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d321999 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86383 (p : Pattern) (ha : d320513 p = 1) (hb : d322005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d322000 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86382 q ha hb
    | true =>
      simp only [d320508, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d322001 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d322002 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d322003 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d322004 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d322005 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro86384 (p : Pattern) (ha : d46527 p = 1) (hb : d321643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46548 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46557 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46523 q = 1) (hb : d321639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46523, d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d46658 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46524 q = 1) (hb : d321640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46524, d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46525 q = 1) (hb : d321641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46525, d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46526 q = 1) (hb : d321642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46526, d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46527 q = 1) (hb : d321643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d321643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d321643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86385 (p : Pattern) (ha : d46537 p = 1) (hb : d321648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46523 q = 1) (hb : d321639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46523, d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d46658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46524 q = 1) (hb : d321640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46524, d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46525 q = 1) (hb : d321641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46525, d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46526 q = 1) (hb : d321642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d46668 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d46673 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d46675 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46533 q = 1) (hb : d321644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46533, d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46534 q = 1) (hb : d321645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46534, d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46535 q = 1) (hb : d321646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d321646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46535, d321646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46536 q = 1) (hb : d321647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d321647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46536, d321647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46537 q = 1) (hb : d321648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d321648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46537, d321648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86386 (p : Pattern) (ha : d321655 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46675 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46533 q = 1) (hb : d321644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46533, d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46534 q = 1) (hb : d321645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46534, d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46535 q = 1) (hb : d321653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d321653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d321653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46536 q = 1) (hb : d321654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d321654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d321654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321655 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321655, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321655, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro86387 (p : Pattern) (ha : d321665 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321661 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321661, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321661, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321662 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321662, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321662, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d321663 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321663, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321663, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321664 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321664, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321664, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321665 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321665, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321665, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86388 (p : Pattern) (ha : d321671 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46540 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d321649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86384 q ha hb
    | true =>
      simp only [d46538, d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86385 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46700 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46539 q = 1) (hb : d321650 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321651 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321651, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d321651, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321652 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321652, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321652, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321656 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321656, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321656, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86386 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d46709 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321657 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321657, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321657, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d321658 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321658, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321658, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321659 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321659, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321659, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321660 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321660, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321660, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321666 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321666, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321666, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86387 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46848 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321667 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321667, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321667, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d321668 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321668, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321668, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321669 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321669, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321669, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321670 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321670, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321670, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321671 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321671, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321671, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86389 (p : Pattern) (ha : d321677 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321672 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321672, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321672, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86388 q ha hb
  have h2 (q : Pattern) (ha : d321673 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321673, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321673, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321674 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321674, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321674, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321675 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321675, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321675, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321676 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321676, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321676, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321677 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321677, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321677, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86390 (p : Pattern) (ha : d46921 p = 1) (hb : d321686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46964 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d47030 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d321686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86391 (p : Pattern) (ha : d46931 p = 1) (hb : d321691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46964 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d47030 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d47040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d47045 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d47047 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d321687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d47054 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d321688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d321689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d321689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d321689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d321690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d321690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d321690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d321691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d321691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d321691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86392 (p : Pattern) (ha : d321698 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d47047 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d321687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d321687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d47054 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d321688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d321688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d321696 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d321696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d321696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d321697 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d321697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d321697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321698 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321698, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321698, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro86393 (p : Pattern) (ha : d321708 p = 1) (hb : d321945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d47132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321940 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321704 q = 1) (hb : d321941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321704, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321704, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d47207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321705 q = 1) (hb : d321942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321705, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321705, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d321706 q = 1) (hb : d321943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321706, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321706, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321707 q = 1) (hb : d321944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321707, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321707, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321708 q = 1) (hb : d321945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321708, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321708, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86394 (p : Pattern) (ha : d321714 p = 1) (hb : d321951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d321692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86390 q ha hb
    | true =>
      simp only [d46932, d321692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86391 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d47072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d321693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d321693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321694 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321694, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d321694, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321695 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321695, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321695, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321699 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321699, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321699, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86392 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d47081 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321700 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321700, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321700, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d321701 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321701, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321701, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321702 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321702, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321702, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321703 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321703, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321703, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321709 q = 1) (hb : d321946 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321709, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321709, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86393 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d47223 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321710 q = 1) (hb : d321947 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321710, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321710, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d321711 q = 1) (hb : d321948 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321711, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321711, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321712 q = 1) (hb : d321949 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321712, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321712, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321713 q = 1) (hb : d321950 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321713, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321713, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321714 q = 1) (hb : d321951 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321714, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321714, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86395 (p : Pattern) (ha : d321720 p = 1) (hb : d321957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321715 q = 1) (hb : d321952 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321715, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321715, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86394 q ha hb
  have h2 (q : Pattern) (ha : d321716 q = 1) (hb : d321953 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321716, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321716, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321717 q = 1) (hb : d321954 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321717, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321717, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321718 q = 1) (hb : d321955 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321718, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321718, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321719 q = 1) (hb : d321956 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321719, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321719, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321720 q = 1) (hb : d321957 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321720, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321720, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86396 (p : Pattern) (ha : d104 p = 1) (hb : d322010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44909 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d322006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d322007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d322008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d322009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d322010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d322010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d322010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86397 (p : Pattern) (ha : d111 p = 1) (hb : d322015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d322006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d322006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d322007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d322007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d322008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d322008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d322009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d322009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44916 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d322011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d322012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d322013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d322013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d322013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d322014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d322014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d322014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d322015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d322015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d322015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86398 (p : Pattern) (ha : d406 p = 1) (hb : d322022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d322011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d322011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d322012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d322012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d322020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d322020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d322020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d322021 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d322021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d322021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d322022 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d322022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d322022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86399 (p : Pattern) (ha : d462 p = 1) (hb : d322032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d322028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d322028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d322028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d322029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d322029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d322029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d322030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d322030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d322030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d322031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d322031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d322031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d322032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d322032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d322032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86400 (p : Pattern) (ha : d53647 p = 1) (hb : d322038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d322016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d322016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86396 q ha hb
    | true =>
      simp only [d112, d322016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86397 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d322017 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d322017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d322017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d322018 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d322018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d322018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d322019 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d322019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d322019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d322023 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d322023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d322023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86398 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d322024 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d322024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d322024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d322025 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d322025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d322025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d322026 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d322026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d322026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d322027 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d322027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d322027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d322033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d322033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d322033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86399 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d322034 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d322034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d322034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d322035 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d322035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d322035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d322036 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d322036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d322036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d322037 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d322037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d322037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d322038 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d322038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d322038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro86401 (p : Pattern) (ha : d320603 p = 1) (hb : d322048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45031 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320599 q = 1) (hb : d322044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320599, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320599, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45067 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d320600 q = 1) (hb : d322045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320600, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320600, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320601 q = 1) (hb : d322046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320601, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320601, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320602 q = 1) (hb : d322047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320602, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320602, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320603 q = 1) (hb : d322048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320603, d322048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320603, d322048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86402 (p : Pattern) (ha : d320610 p = 1) (hb : d322053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320539 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d320599 q = 1) (hb : d322044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320599, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320599, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d320600 q = 1) (hb : d322045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320600, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320600, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320601 q = 1) (hb : d322046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320601, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320601, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320602 q = 1) (hb : d322047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320602, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320602, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45076 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45080 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45082 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d320546 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d320606 q = 1) (hb : d322049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320606, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320606, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45088 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320607 q = 1) (hb : d322050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320607, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320607, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320608 q = 1) (hb : d322051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320608, d322051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320608, d322051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320609 q = 1) (hb : d322052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320609, d322052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320609, d322052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d320610 q = 1) (hb : d322053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320610, d322053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320610, d322053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86403 (p : Pattern) (ha : d321771 p = 1) (hb : d322060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320546 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320606 q = 1) (hb : d322049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320606, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320606, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320607 q = 1) (hb : d322050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320607, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320607, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320608 q = 1) (hb : d322058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320608, d322058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320608, d322058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320609 q = 1) (hb : d322059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320609, d322059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320609, d322059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321771 q = 1) (hb : d322060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321771, d322060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321771, d322060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86404 (p : Pattern) (ha : d321781 p = 1) (hb : d322070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320582 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321777 q = 1) (hb : d322066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321777, d322066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321777, d322066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321778 q = 1) (hb : d322067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321778, d322067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321778, d322067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321779 q = 1) (hb : d322068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321779, d322068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321779, d322068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321780 q = 1) (hb : d322069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321780, d322069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321780, d322069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321781 q = 1) (hb : d322070 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321781, d322070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321781, d322070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86405 (p : Pattern) (ha : d321787 p = 1) (hb : d322076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320611 q = 1) (hb : d322054 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320611, d322054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86401 q ha hb
    | true =>
      simp only [d320611, d322054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86402 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320612 q = 1) (hb : d322055 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320612, d322055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320612, d322055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321769 q = 1) (hb : d322056 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321769, d322056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321769, d322056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321770 q = 1) (hb : d322057 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321770, d322057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321770, d322057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321772 q = 1) (hb : d322061 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321772, d322061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321772, d322061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86403 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321773 q = 1) (hb : d322062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321773, d322062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321773, d322062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321774 q = 1) (hb : d322063 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321774, d322063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321774, d322063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321775 q = 1) (hb : d322064 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321775, d322064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321775, d322064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321776 q = 1) (hb : d322065 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321776, d322065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321776, d322065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321782 q = 1) (hb : d322071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321782, d322071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321782, d322071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86404 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321783 q = 1) (hb : d322072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321783, d322072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321783, d322072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d321784 q = 1) (hb : d322073 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321784, d322073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321784, d322073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321785 q = 1) (hb : d322074 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321785, d322074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321785, d322074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321786 q = 1) (hb : d322075 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321786, d322075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321786, d322075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321787 q = 1) (hb : d322076 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321787, d322076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321787, d322076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86406 (p : Pattern) (ha : d321793 p = 1) (hb : d322082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86400 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321788 q = 1) (hb : d322077 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321788, d322077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321788, d322077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86405 q ha hb
  have h8 (q : Pattern) (ha : d321789 q = 1) (hb : d322078 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321789, d322078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321789, d322078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321790 q = 1) (hb : d322079 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321790, d322079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321790, d322079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321791 q = 1) (hb : d322080 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321791, d322080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321791, d322080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d321792 q = 1) (hb : d322081 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321792, d322081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321792, d322081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d321793 q = 1) (hb : d322082 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321793, d322082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321793, d322082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro86407 (p : Pattern) (ha : d320773 p = 1) (hb : d322087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45216 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45276 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320769 q = 1) (hb : d322083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320769, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320769, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d320770 q = 1) (hb : d322084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320770, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320770, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320771 q = 1) (hb : d322085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320771, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320771, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320772 q = 1) (hb : d322086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320772, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320772, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320773 q = 1) (hb : d322087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320773, d322087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320773, d322087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86408 (p : Pattern) (ha : d320783 p = 1) (hb : d322092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45216 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d320769 q = 1) (hb : d322083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320769, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320769, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d320770 q = 1) (hb : d322084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320770, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320770, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320771 q = 1) (hb : d322085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320771, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320771, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d320772 q = 1) (hb : d322086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320772, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320772, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45345 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d320779 q = 1) (hb : d322088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320779, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d320779, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d320780 q = 1) (hb : d322089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320780, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d320780, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320781 q = 1) (hb : d322090 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320781, d322090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320781, d322090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d320782 q = 1) (hb : d322091 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320782, d322091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d320782, d322091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d320783 q = 1) (hb : d322092 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d320783, d322092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320783, d322092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86409 (p : Pattern) (ha : d321796 p = 1) (hb : d322099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45345 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320779 q = 1) (hb : d322088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d320779, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320779, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45352 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d320780 q = 1) (hb : d322089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d320780, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320780, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d320781 q = 1) (hb : d322097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d320781, d322097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320781, d322097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320782 q = 1) (hb : d322098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d320782, d322098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d320782, d322098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321796 q = 1) (hb : d322099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321796, d322099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321796, d322099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86410 (p : Pattern) (ha : d321807 p = 1) (hb : d322109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321803 q = 1) (hb : d322105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321803, d322105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321803, d322105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45468 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321804 q = 1) (hb : d322106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321804, d322106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321804, d322106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321805 q = 1) (hb : d322107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321805, d322107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321805, d322107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321806 q = 1) (hb : d322108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321806, d322108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321806, d322108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321807 q = 1) (hb : d322109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321807, d322109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321807, d322109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86411 (p : Pattern) (ha : d321813 p = 1) (hb : d322115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45208 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320784 q = 1) (hb : d322093 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d320784, d322093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86407 q ha hb
    | true =>
      simp only [d320784, d322093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86408 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d320785 q = 1) (hb : d322094 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d320785, d322094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320785, d322094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321794 q = 1) (hb : d322095 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321794, d322095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321794, d322095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321795 q = 1) (hb : d322096 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321795, d322096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321795, d322096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321797 q = 1) (hb : d322100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321797, d322100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321797, d322100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86409 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d45379 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321798 q = 1) (hb : d322101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321798, d322101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321798, d322101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321799 q = 1) (hb : d322102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321799, d322102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321799, d322102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321800 q = 1) (hb : d322103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321800, d322103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321800, d322103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321801 q = 1) (hb : d322104 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321801, d322104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321801, d322104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321808 q = 1) (hb : d322110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321808, d322110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321808, d322110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86410 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45484 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321809 q = 1) (hb : d322111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321809, d322111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321809, d322111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d321810 q = 1) (hb : d322112 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321810, d322112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321810, d322112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321811 q = 1) (hb : d322113 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321811, d322113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321811, d322113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321812 q = 1) (hb : d322114 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321812, d322114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321812, d322114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321813 q = 1) (hb : d322115 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321813, d322115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321813, d322115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86412 (p : Pattern) (ha : d321819 p = 1) (hb : d322121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321814 q = 1) (hb : d322116 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321814, d322116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321814, d322116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86411 q ha hb
  have h2 (q : Pattern) (ha : d321815 q = 1) (hb : d322117 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321815, d322117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321815, d322117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321816 q = 1) (hb : d322118 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321816, d322118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321816, d322118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321817 q = 1) (hb : d322119 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321817, d322119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321817, d322119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321818 q = 1) (hb : d322120 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321818, d322120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321818, d322120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321819 q = 1) (hb : d322121 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321819, d322121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321819, d322121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86413 (p : Pattern) (ha : d321028 p = 1) (hb : d322127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45558 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45628 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321024 q = 1) (hb : d322123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321024, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321024, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45703 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d321025 q = 1) (hb : d322124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321025, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321025, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321026 q = 1) (hb : d322125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321026, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321026, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321027 q = 1) (hb : d322126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321027, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321027, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321028 q = 1) (hb : d322127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321028, d322127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321028, d322127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86414 (p : Pattern) (ha : d321038 p = 1) (hb : d322132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d321024 q = 1) (hb : d322123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321024, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321024, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45703 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d321025 q = 1) (hb : d322124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321025, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321025, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321026 q = 1) (hb : d322125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321026, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321026, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321027 q = 1) (hb : d322126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321027, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321027, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45713 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45718 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45720 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d321034 q = 1) (hb : d322128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321034, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321034, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45727 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321035 q = 1) (hb : d322129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321035, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321035, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d321036 q = 1) (hb : d322130 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321036, d322130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321036, d322130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d321037 q = 1) (hb : d322131 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321037, d322131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321037, d322131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d321038 q = 1) (hb : d322132 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321038, d322132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321038, d322132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86415 (p : Pattern) (ha : d321823 p = 1) (hb : d322139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45720 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321034 q = 1) (hb : d322128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321034, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321034, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321035 q = 1) (hb : d322129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321035, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321035, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321036 q = 1) (hb : d322137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321036, d322137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321036, d322137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321037 q = 1) (hb : d322138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321037, d322138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321037, d322138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321823 q = 1) (hb : d322139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321823, d322139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321823, d322139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86416 (p : Pattern) (ha : d321834 p = 1) (hb : d322149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321830 q = 1) (hb : d322145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321830, d322145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321830, d322145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45875 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321831 q = 1) (hb : d322146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321831, d322146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321831, d322146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321832 q = 1) (hb : d322147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321832, d322147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321832, d322147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321833 q = 1) (hb : d322148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321833, d322148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321833, d322148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321834 q = 1) (hb : d322149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321834, d322149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321834, d322149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86417 (p : Pattern) (ha : d321840 p = 1) (hb : d322155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45550 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321039 q = 1) (hb : d322133 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321039, d322133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86413 q ha hb
    | true =>
      simp only [d321039, d322133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86414 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321040 q = 1) (hb : d322134 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321040, d322134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321040, d322134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321821 q = 1) (hb : d322135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321821, d322135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321821, d322135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321822 q = 1) (hb : d322136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321822, d322136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321822, d322136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321824 q = 1) (hb : d322140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321824, d322140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321824, d322140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86415 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d45754 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321825 q = 1) (hb : d322141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321825, d322141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321825, d322141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321826 q = 1) (hb : d322142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321826, d322142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321826, d322142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321827 q = 1) (hb : d322143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321827, d322143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321827, d322143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321828 q = 1) (hb : d322144 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321828, d322144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321828, d322144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321835 q = 1) (hb : d322150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321835, d322150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321835, d322150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86416 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45891 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321836 q = 1) (hb : d322151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321836, d322151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321836, d322151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d321837 q = 1) (hb : d322152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321837, d322152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321837, d322152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321838 q = 1) (hb : d322153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321838, d322153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321838, d322153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321839 q = 1) (hb : d322154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321839, d322154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321839, d322154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321840 q = 1) (hb : d322155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321840, d322155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321840, d322155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86418 (p : Pattern) (ha : d321846 p = 1) (hb : d322161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321841 q = 1) (hb : d322156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321841, d322156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321841, d322156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86417 q ha hb
  have h2 (q : Pattern) (ha : d321842 q = 1) (hb : d322157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321842, d322157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321842, d322157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321843 q = 1) (hb : d322158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321843, d322158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321843, d322158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321844 q = 1) (hb : d322159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321844, d322159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321844, d322159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321845 q = 1) (hb : d322160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321845, d322160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321845, d322160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321846 q = 1) (hb : d322161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321846, d322161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321846, d322161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86419 (p : Pattern) (ha : d321361 p = 1) (hb : d322168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46088 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321357 q = 1) (hb : d322164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321357, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321357, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d46211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d321358 q = 1) (hb : d322165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321358, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321358, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321359 q = 1) (hb : d322166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321359, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321359, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321360 q = 1) (hb : d322167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321360, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321360, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321361 q = 1) (hb : d322168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321361, d322168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321361, d322168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86420 (p : Pattern) (ha : d321371 p = 1) (hb : d322173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46088 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d321357 q = 1) (hb : d322164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321357, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321357, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d46211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d321358 q = 1) (hb : d322165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321358, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321358, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321359 q = 1) (hb : d322166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321359, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321359, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321360 q = 1) (hb : d322167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321360, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321360, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d46221 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d46226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d46228 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d321367 q = 1) (hb : d322169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321367, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321367, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321368 q = 1) (hb : d322170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321368, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321368, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d321369 q = 1) (hb : d322171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321369, d322171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321369, d322171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d321370 q = 1) (hb : d322172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321370, d322172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321370, d322172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d321371 q = 1) (hb : d322173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321371, d322173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321371, d322173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86421 (p : Pattern) (ha : d321851 p = 1) (hb : d322180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321367 q = 1) (hb : d322169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321367, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321367, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321368 q = 1) (hb : d322170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321368, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321368, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321369 q = 1) (hb : d322178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321369, d322178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321369, d322178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321370 q = 1) (hb : d322179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321370, d322179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321370, d322179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321851 q = 1) (hb : d322180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321851, d322180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321851, d322180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86422 (p : Pattern) (ha : d321862 p = 1) (hb : d322190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321858 q = 1) (hb : d322186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321858, d322186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321858, d322186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46428 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321859 q = 1) (hb : d322187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321859, d322187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321859, d322187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321860 q = 1) (hb : d322188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321860, d322188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321860, d322188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321861 q = 1) (hb : d322189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321861, d322189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321861, d322189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321862 q = 1) (hb : d322190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321862, d322190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321862, d322190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86423 (p : Pattern) (ha : d321868 p = 1) (hb : d322196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321372 q = 1) (hb : d322174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321372, d322174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86419 q ha hb
    | true =>
      simp only [d321372, d322174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86420 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d321373 q = 1) (hb : d322175 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321373, d322175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321373, d322175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321849 q = 1) (hb : d322176 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321849, d322176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321849, d322176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321850 q = 1) (hb : d322177 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321850, d322177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321850, d322177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321852 q = 1) (hb : d322181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321852, d322181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321852, d322181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86421 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d46262 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321853 q = 1) (hb : d322182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321853, d322182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321853, d322182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321854 q = 1) (hb : d322183 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321854, d322183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321854, d322183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321855 q = 1) (hb : d322184 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321855, d322184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321855, d322184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321856 q = 1) (hb : d322185 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321856, d322185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321856, d322185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321863 q = 1) (hb : d322191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321863, d322191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321863, d322191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86422 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d321864 q = 1) (hb : d322192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321864, d322192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321864, d322192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d321865 q = 1) (hb : d322193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321865, d322193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321865, d322193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d321866 q = 1) (hb : d322194 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321866, d322194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321866, d322194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d321867 q = 1) (hb : d322195 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321867, d322195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321867, d322195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d321868 q = 1) (hb : d322196 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321868, d322196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321868, d322196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86424 (p : Pattern) (ha : d321874 p = 1) (hb : d322202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321869 q = 1) (hb : d322197 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321869, d322197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321869, d322197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86423 q ha hb
  have h2 (q : Pattern) (ha : d321870 q = 1) (hb : d322198 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321870, d322198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321870, d322198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d321871 q = 1) (hb : d322199 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321871, d322199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321871, d322199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321872 q = 1) (hb : d322200 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321872, d322200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321872, d322200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d321873 q = 1) (hb : d322201 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321873, d322201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321873, d322201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321874 q = 1) (hb : d322202 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321874, d322202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321874, d322202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86425 (p : Pattern) (ha : d321963 p = 1) (hb : d322208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d321820 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321820, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86406 q ha hb
    | true =>
      simp only [d321820, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86412 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d321847 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321847, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321847, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86418 q ha hb
  have h3 (q : Pattern) (ha : d321848 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321848, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321848, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d321875 q = 1) (hb : d322203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321875, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321875, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86424 q ha hb
  have h5 (q : Pattern) (ha : d321876 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321876, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321876, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321877 q = 1) (hb : d322205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321877, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321877, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321678 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86389 q ha hb
  have h8 (q : Pattern) (ha : d321679 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321680 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321907 q = 1) (hb : d322206 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d321907, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321907, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d321721 q = 1) (hb : d321958 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321721, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321721, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86395 q ha hb
  have h12 (q : Pattern) (ha : d321722 q = 1) (hb : d321959 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321722, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321722, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321723 q = 1) (hb : d321960 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321723, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321723, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d321724 q = 1) (hb : d321961 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d321724, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321724, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d321962 q = 1) (hb : d322207 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d321962, d322207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321962, d322207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d321963 q = 1) (hb : d322208 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d321963, d322208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d321963, d322208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro86426 (p : Pattern) (ha : d321969 p = 1) (hb : d322214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321964 q = 1) (hb : d322209 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d321964, d322209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86425 q ha hb
    | true =>
      simp only [d321964, d322209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d321965 q = 1) (hb : d322210 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d321965, d322210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321965, d322210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321966 q = 1) (hb : d322211 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d321966, d322211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321966, d322211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321967 q = 1) (hb : d322212 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d321967, d322212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321967, d322212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d321968 q = 1) (hb : d322213 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d321968, d322213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321968, d322213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d321969 q = 1) (hb : d322214 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d321969, d322214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321969, d322214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86427 (p : Pattern) (ha : d321975 p = 1) (hb : d322220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321970 q = 1) (hb : d322215 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d321970, d322215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86426 q ha hb
    | true =>
      simp only [d321970, d322215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d321971 q = 1) (hb : d322216 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d321971, d322216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321971, d322216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321972 q = 1) (hb : d322217 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d321972, d322217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321972, d322217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321973 q = 1) (hb : d322218 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d321973, d322218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321973, d322218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d321974 q = 1) (hb : d322219 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d321974, d322219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321974, d322219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d321975 q = 1) (hb : d322220 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d321975, d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321975, d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86428 (p : Pattern) (ha : d321981 p = 1) (hb : d322226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321976 q = 1) (hb : d322221 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d321976, d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86427 q ha hb
    | true =>
      simp only [d321976, d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d321977 q = 1) (hb : d322222 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d321977, d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321977, d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321978 q = 1) (hb : d322223 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d321978, d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321978, d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321979 q = 1) (hb : d322224 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d321979, d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321979, d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d321980 q = 1) (hb : d322225 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d321980, d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321980, d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d321981 q = 1) (hb : d322226 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d321981, d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321981, d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86429 (p : Pattern) (ha : d321987 p = 1) (hb : d322232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321982 q = 1) (hb : d322227 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d321982, d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86428 q ha hb
    | true =>
      simp only [d321982, d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d321983 q = 1) (hb : d322228 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d321983, d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321983, d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321984 q = 1) (hb : d322229 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d321984, d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321984, d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321985 q = 1) (hb : d322230 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d321985, d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321985, d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d321986 q = 1) (hb : d322231 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d321986, d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321986, d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d321987 q = 1) (hb : d322232 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d321987, d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321987, d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86430 (p : Pattern) (ha : d321993 p = 1) (hb : d322238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321988 q = 1) (hb : d322233 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d321988, d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86429 q ha hb
    | true =>
      simp only [d321988, d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d321989 q = 1) (hb : d322234 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d321989, d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321989, d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321990 q = 1) (hb : d322235 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d321990, d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321990, d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321991 q = 1) (hb : d322236 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d321991, d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321991, d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d321992 q = 1) (hb : d322237 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d321992, d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321992, d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d321993 q = 1) (hb : d322238 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d321993, d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321993, d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86431 (p : Pattern) (ha : d321999 p = 1) (hb : d322244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d321994 q = 1) (hb : d322239 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d321994, d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86430 q ha hb
    | true =>
      simp only [d321994, d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d321995 q = 1) (hb : d322240 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d321995, d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321995, d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321996 q = 1) (hb : d322241 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d321996, d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321996, d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d321997 q = 1) (hb : d322242 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d321997, d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321997, d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d321998 q = 1) (hb : d322243 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d321998, d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321998, d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d321999 q = 1) (hb : d322244 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d321999, d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321999, d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86432 (p : Pattern) (ha : d322005 p = 1) (hb : d322250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322000 q = 1) (hb : d322245 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322000, d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86431 q ha hb
    | true =>
      simp only [d322000, d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322001 q = 1) (hb : d322246 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322001, d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322001, d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322002 q = 1) (hb : d322247 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322002, d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322002, d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322003 q = 1) (hb : d322248 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322003, d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322003, d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322004 q = 1) (hb : d322249 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322004, d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322004, d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322005 q = 1) (hb : d322250 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322005, d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322005, d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86433 (p : Pattern) (ha : d33214 p = 1) (hb : d322255 p = 1) : d322256 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33213 q = 1) (hb : d322254 q = 1) : d317407 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33213, d322254, d317407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33213, d322254, d317407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17 q = 1) (hb : d271215 q = 1) : d17 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33214 q = 1) (hb : d322255 q = 1) : d322256 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33214, d322255, d322256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33214, d322255, d322256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86434 (p : Pattern) (ha : d33220 p = 1) (hb : d322255 p = 1) : d322262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d322255 q = 1) : d322257 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86433 q ha hb
    | true =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d322255 q = 1) : d322258 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d322255 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d322255 q = 1) : d322259 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d322255 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33218 q = 1) (hb : d322255 q = 1) : d322260 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d322260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33218, d322260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33219 q = 1) (hb : d322255 q = 1) : d322261 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d322261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33219, d322261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d322255 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33220 q = 1) (hb : d322255 q = 1) : d322262 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33220, d322262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33220, d322262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro86435 (p : Pattern) (ha : d33226 p = 1) (hb : d322255 p = 1) : d322268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33221 q = 1) (hb : d322255 q = 1) : d322263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86434 q ha hb
    | true =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33222 q = 1) (hb : d322255 q = 1) : d322264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33223 q = 1) (hb : d322255 q = 1) : d322265 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d322265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d322265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33224 q = 1) (hb : d322255 q = 1) : d322266 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d322266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33224, d322266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d322255 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33225 q = 1) (hb : d322255 q = 1) : d322267 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33225, d322267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33225, d322267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d322255 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33226 q = 1) (hb : d322255 q = 1) : d322268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33226, d322268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33226, d322268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86436 (p : Pattern) (ha : d33232 p = 1) (hb : d322255 p = 1) : d322274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d322255 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d322255 q = 1) : d322269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
    | true =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d322255 q = 1) : d322270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d322255 q = 1) : d322271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d322255 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33230 q = 1) (hb : d322255 q = 1) : d322272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d322272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33230, d322272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d322255 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33231 q = 1) (hb : d322255 q = 1) : d322273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33231, d322273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33231, d322273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33232 q = 1) (hb : d322255 q = 1) : d322274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33232, d322274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33232, d322274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro86437 (p : Pattern) (ha : d33238 p = 1) (hb : d322255 p = 1) : d322280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d322255 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d322255 q = 1) : d322277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d322255 q = 1) : d322278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d322255 q = 1) : d322279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d322279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d322279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33238 q = 1) (hb : d322255 q = 1) : d322280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33238, d322280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33238, d322280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86438 (p : Pattern) (ha : d265915 p = 1) (hb : d322255 p = 1) : d322286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d322255 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d322255 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d322255 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33239 q = 1) (hb : d322255 q = 1) : d322281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
    | true =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d322255 q = 1) : d322282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d322282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265911, d322282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d322255 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d322255 q = 1) : d322283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d322283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d322283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d322255 q = 1) : d322284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d322284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265913, d322284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d322255 q = 1) : d322285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d322285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265914, d322285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265915 q = 1) (hb : d322255 q = 1) : d322286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265915, d322286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265915, d322286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86439 (p : Pattern) (ha : d33245 p = 1) (hb : d322255 p = 1) : d322287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d322255 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d322255 q = 1) : d322277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d322255 q = 1) : d322278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d322255 q = 1) : d322279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d322279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d322279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33245 q = 1) (hb : d322255 q = 1) : d322287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33245, d322287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33245, d322287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro86440 (p : Pattern) (ha : d265920 p = 1) (hb : d322255 p = 1) : d322293 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d322255 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d322255 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d322255 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33239 q = 1) (hb : d322255 q = 1) : d322281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
    | true =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d322255 q = 1) : d322282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d322282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265911, d322282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d322255 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d322255 q = 1) : d322283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d322283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d322283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d322255 q = 1) : d322284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d322284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265913, d322284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d322255 q = 1) : d322285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d322285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265914, d322285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d322255 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d322255 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d322255 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d33246 q = 1) (hb : d322255 q = 1) : d322288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86439 q ha hb
    | true =>
      simp only [d33246, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265916 q = 1) (hb : d322255 q = 1) : d322289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d322289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265916, d322289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d322255 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d265917 q = 1) (hb : d322255 q = 1) : d322290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d322290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265917, d322290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265918 q = 1) (hb : d322255 q = 1) : d322291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265918, d322291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265918, d322291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265919 q = 1) (hb : d322255 q = 1) : d322292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265919, d322292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265919, d322292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d265920 q = 1) (hb : d322255 q = 1) : d322293 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265920, d322293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265920, d322293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86441 (p : Pattern) (ha : d265927 p = 1) (hb : d322255 p = 1) : d322300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d322255 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33246 q = 1) (hb : d322255 q = 1) : d322288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86439 q ha hb
    | true =>
      simp only [d33246, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265916 q = 1) (hb : d322255 q = 1) : d322289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d322289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265916, d322289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d322255 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265917 q = 1) (hb : d322255 q = 1) : d322290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d322290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265917, d322290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265925 q = 1) (hb : d322255 q = 1) : d322298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265925, d322298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265925, d322298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265926 q = 1) (hb : d322255 q = 1) : d322299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265926, d322299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265926, d322299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265927 q = 1) (hb : d322255 q = 1) : d322300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265927, d322300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265927, d322300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86442 (p : Pattern) (ha : d33269 p = 1) (hb : d322255 p = 1) : d322311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33264 q = 1) (hb : d322255 q = 1) : d322306 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d322306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d322306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86434 q ha hb
  have h2 (q : Pattern) (ha : d33221 q = 1) (hb : d322255 q = 1) : d322263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86434 q ha hb
    | true =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33265 q = 1) (hb : d322255 q = 1) : d322307 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d322307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33265, d322307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33222 q = 1) (hb : d322255 q = 1) : d322264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33266 q = 1) (hb : d322255 q = 1) : d322308 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d322308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33266, d322308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33267 q = 1) (hb : d322255 q = 1) : d322309 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d322309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33267, d322309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d322255 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33268 q = 1) (hb : d322255 q = 1) : d322310 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33268, d322310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33268, d322310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d322255 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33269 q = 1) (hb : d322255 q = 1) : d322311 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33269, d322311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33269, d322311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro86443 (p : Pattern) (ha : d33275 p = 1) (hb : d322255 p = 1) : d322317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d322255 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33270 q = 1) (hb : d322255 q = 1) : d322312 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d322312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86442 q ha hb
    | true =>
      simp only [d33270, d322312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33271 q = 1) (hb : d322255 q = 1) : d322313 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d322313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d322313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33272 q = 1) (hb : d322255 q = 1) : d322314 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d322314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d322314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d322255 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33273 q = 1) (hb : d322255 q = 1) : d322315 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d322315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33273, d322315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d322255 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33274 q = 1) (hb : d322255 q = 1) : d322316 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33274, d322316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33274, d322316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33275 q = 1) (hb : d322255 q = 1) : d322317 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33275, d322317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33275, d322317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro86444 (p : Pattern) (ha : d33281 p = 1) (hb : d322255 p = 1) : d322323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d322255 q = 1) : d322318 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d322318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86443 q ha hb
    | true =>
      simp only [d33276, d322318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d322255 q = 1) : d322319 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d322319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d322319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d322255 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33278 q = 1) (hb : d322255 q = 1) : d322320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33278, d322320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33278, d322320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33279 q = 1) (hb : d322255 q = 1) : d322321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33279, d322321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33279, d322321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33280 q = 1) (hb : d322255 q = 1) : d322322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33280, d322322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33280, d322322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33281 q = 1) (hb : d322255 q = 1) : d322323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33281, d322323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33281, d322323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro86445 (p : Pattern) (ha : d265937 p = 1) (hb : d322255 p = 1) : d322329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d322255 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33282 q = 1) (hb : d322255 q = 1) : d322324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d322324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86444 q ha hb
    | true =>
      simp only [d33282, d322324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265933 q = 1) (hb : d322255 q = 1) : d322325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265933, d322325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265933, d322325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d322255 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265934 q = 1) (hb : d322255 q = 1) : d322326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265934, d322326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265934, d322326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265935 q = 1) (hb : d322255 q = 1) : d322327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265935, d322327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265935, d322327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265936 q = 1) (hb : d322255 q = 1) : d322328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265936, d322328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265936, d322328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265937 q = 1) (hb : d322255 q = 1) : d322329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265937, d322329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265937, d322329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86446 (p : Pattern) (ha : d265943 p = 1) (hb : d322255 p = 1) : d322335 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d322255 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265921 q = 1) (hb : d322255 q = 1) : d322294 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265921, d322294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86438 q ha hb
    | true =>
      simp only [d265921, d322294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86440 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d322255 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265922 q = 1) (hb : d322255 q = 1) : d322295 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265922, d322295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265922, d322295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265923 q = 1) (hb : d322255 q = 1) : d322296 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265923, d322296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265923, d322296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265924 q = 1) (hb : d322255 q = 1) : d322297 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265924, d322297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265924, d322297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265928 q = 1) (hb : d322255 q = 1) : d322301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265928, d322301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265928, d322301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86441 q ha hb
  have h8 (q : Pattern) (ha : d265929 q = 1) (hb : d322255 q = 1) : d322302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265929, d322302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265929, d322302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d265930 q = 1) (hb : d322255 q = 1) : d322303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265930, d322303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265930, d322303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d265931 q = 1) (hb : d322255 q = 1) : d322304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265931, d322304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265931, d322304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265932 q = 1) (hb : d322255 q = 1) : d322305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265932, d322305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265932, d322305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265938 q = 1) (hb : d322255 q = 1) : d322330 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265938, d322330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265938, d322330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86445 q ha hb
  have h13 (q : Pattern) (ha : d265939 q = 1) (hb : d322255 q = 1) : d322331 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265939, d322331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265939, d322331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d265940 q = 1) (hb : d322255 q = 1) : d322332 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265940, d322332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265940, d322332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d265941 q = 1) (hb : d322255 q = 1) : d322333 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265941, d322333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265941, d322333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d265942 q = 1) (hb : d322255 q = 1) : d322334 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265942, d322334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265942, d322334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265943 q = 1) (hb : d322255 q = 1) : d322335 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265943, d322335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265943, d322335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro86447 (p : Pattern) (ha : d33303 p = 1) (hb : d322255 p = 1) : d322345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d322255 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d322255 q = 1) : d322281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
    | true =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d322255 q = 1) : d322341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d322255 q = 1) : d322342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d322255 q = 1) : d322343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d322255 q = 1) : d322344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33303 q = 1) (hb : d322255 q = 1) : d322345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33303, d322345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33303, d322345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86448 (p : Pattern) (ha : d33310 p = 1) (hb : d322255 p = 1) : d322352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d322255 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d322255 q = 1) : d322281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
    | true =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d322255 q = 1) : d322341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d322255 q = 1) : d322342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d322255 q = 1) : d322343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d322255 q = 1) : d322344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d322255 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33246 q = 1) (hb : d322255 q = 1) : d322288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86439 q ha hb
    | true =>
      simp only [d33246, d322288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33306 q = 1) (hb : d322255 q = 1) : d322348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d322348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33307 q = 1) (hb : d322255 q = 1) : d322349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33307, d322349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33308 q = 1) (hb : d322255 q = 1) : d322350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d322350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33309 q = 1) (hb : d322255 q = 1) : d322351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d322351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33310 q = 1) (hb : d322255 q = 1) : d322352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33310, d322352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33310, d322352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro86449 (p : Pattern) (ha : d33421 p = 1) (hb : d322255 p = 1) : d322433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d322255 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d322255 q = 1) : d322281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
    | true =>
      simp only [d33239, d322281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d322255 q = 1) : d322341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d322341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d322255 q = 1) : d322342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d322342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d322255 q = 1) : d322343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d322343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d322255 q = 1) : d322344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d322344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d322255 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33421 q = 1) (hb : d322255 q = 1) : d322433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33421, d322433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33421, d322433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86450 (p : Pattern) (ha : d33315 p = 1) (hb : d322255 p = 1) : d322357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d322255 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d322255 q = 1) : d322277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d322255 q = 1) : d322278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33314 q = 1) (hb : d322255 q = 1) : d322356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d322356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d322356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33315 q = 1) (hb : d322255 q = 1) : d322357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33315, d322357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33315, d322357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86451 (p : Pattern) (ha : d33322 p = 1) (hb : d322255 p = 1) : d322364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d322255 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d322255 q = 1) : d322277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33320 q = 1) (hb : d322255 q = 1) : d322362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d322362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d322362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33321 q = 1) (hb : d322255 q = 1) : d322363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d322363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33321, d322363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33322 q = 1) (hb : d322255 q = 1) : d322364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33322, d322364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33322, d322364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro86452 (p : Pattern) (ha : d33327 p = 1) (hb : d322255 p = 1) : d322368 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33326 q = 1) (hb : d322254 q = 1) : d2018 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33326, d322254, d2018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33326, d322254, d2018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d127 q = 1) : d127 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d128 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d129 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h13 (q : Pattern) (ha : d15 q = 1) (hb : d271214 q = 1) : d15 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d130 q = 1) (hb : d271214 q = 1) : d1540 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33213 q = 1) (hb : d271215 q = 1) : d1541 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33213, d271215, d1541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33213, d271215, d1541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d33327 q = 1) (hb : d322255 q = 1) : d322368 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33327, d322255, d322368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33327, d322255, d322368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro86453 (p : Pattern) (ha : d33333 p = 1) (hb : d322255 p = 1) : d322374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d322255 q = 1) : d322369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86452 q ha hb
    | true =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d322255 q = 1) : d322370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d322255 q = 1) : d322257 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86433 q ha hb
    | true =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d322255 q = 1) : d322258 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d322255 q = 1) : d322371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d322255 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33217 q = 1) (hb : d322255 q = 1) : d322259 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33331 q = 1) (hb : d322255 q = 1) : d322372 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d322372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33331, d322372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33332 q = 1) (hb : d322255 q = 1) : d322373 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d322373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33332, d322373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d322255 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33218 q = 1) (hb : d322255 q = 1) : d322260 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d322260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33218, d322260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33219 q = 1) (hb : d322255 q = 1) : d322261 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d322261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33219, d322261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33333 q = 1) (hb : d322255 q = 1) : d322374 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33333, d322374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33333, d322374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro86454 (p : Pattern) (ha : d33341 p = 1) (hb : d322255 p = 1) : d322382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d322255 q = 1) : d322257 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86433 q ha hb
    | true =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d322255 q = 1) : d322258 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d322255 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d322255 q = 1) : d322259 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33339 q = 1) (hb : d322255 q = 1) : d322380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d322380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33339, d322380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33340 q = 1) (hb : d322255 q = 1) : d322381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d322381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33340, d322381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d322255 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33341 q = 1) (hb : d322255 q = 1) : d322382 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33341, d322382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33341, d322382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86455 (p : Pattern) (ha : d33347 p = 1) (hb : d322255 p = 1) : d322388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33334 q = 1) (hb : d322255 q = 1) : d322375 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d322375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86453 q ha hb
    | true =>
      simp only [d33334, d322375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33335 q = 1) (hb : d322255 q = 1) : d322376 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d322376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33335, d322376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33336 q = 1) (hb : d322255 q = 1) : d322377 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33336, d322377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33336, d322377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33337 q = 1) (hb : d322255 q = 1) : d322378 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33337, d322378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33337, d322378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33221 q = 1) (hb : d322255 q = 1) : d322263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86434 q ha hb
    | true =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33222 q = 1) (hb : d322255 q = 1) : d322264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33223 q = 1) (hb : d322255 q = 1) : d322265 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d322265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d322265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33224 q = 1) (hb : d322255 q = 1) : d322266 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d322266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33224, d322266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33338 q = 1) (hb : d322255 q = 1) : d322379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33338, d322379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33338, d322379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33342 q = 1) (hb : d322255 q = 1) : d322383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86454 q ha hb
    | true =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33343 q = 1) (hb : d322255 q = 1) : d322384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33344 q = 1) (hb : d322255 q = 1) : d322385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d322385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d322385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33345 q = 1) (hb : d322255 q = 1) : d322386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d322386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33345, d322386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d322255 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d33346 q = 1) (hb : d322255 q = 1) : d322387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d322387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33346, d322387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33347 q = 1) (hb : d322255 q = 1) : d322388 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33347, d322388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33347, d322388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro86456 (p : Pattern) (ha : d33353 p = 1) (hb : d322255 p = 1) : d322394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d322255 q = 1) : d322389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d322389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86455 q ha hb
    | true =>
      simp only [d33348, d322389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d322255 q = 1) : d322390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d322390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d322390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d322255 q = 1) : d322391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d322391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d322391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d322255 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33227 q = 1) (hb : d322255 q = 1) : d322269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
    | true =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33228 q = 1) (hb : d322255 q = 1) : d322270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33229 q = 1) (hb : d322255 q = 1) : d322271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33351 q = 1) (hb : d322255 q = 1) : d322392 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d322392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d322392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d322255 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33230 q = 1) (hb : d322255 q = 1) : d322272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d322272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33230, d322272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33352 q = 1) (hb : d322255 q = 1) : d322393 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33352, d322393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33352, d322393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33353 q = 1) (hb : d322255 q = 1) : d322394 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33353, d322394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33353, d322394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro86457 (p : Pattern) (ha : d33359 p = 1) (hb : d322255 p = 1) : d322400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d322255 q = 1) : d322395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d322395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86456 q ha hb
    | true =>
      simp only [d33354, d322395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d322255 q = 1) : d322396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d322396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d322396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d322255 q = 1) : d322397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d322397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d322397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d322255 q = 1) : d322398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d322398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d322398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d322255 q = 1) : d322399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d322399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d322399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33359 q = 1) (hb : d322255 q = 1) : d322400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33359, d322400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33359, d322400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86458 (p : Pattern) (ha : d33392 p = 1) (hb : d322255 p = 1) : d322406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d322255 q = 1) : d322403 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d322403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d322403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d322255 q = 1) : d322404 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d322404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d322404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d322255 q = 1) : d322405 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d322405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d322405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33392 q = 1) (hb : d322255 q = 1) : d322406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33392, d322406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33392, d322406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86459 (p : Pattern) (ha : d265953 p = 1) (hb : d322255 p = 1) : d322412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d322255 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33316 q = 1) (hb : d322255 q = 1) : d322358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d322358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86450 q ha hb
    | true =>
      simp only [d33316, d322358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33317 q = 1) (hb : d322255 q = 1) : d322359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d322359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d322359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33318 q = 1) (hb : d322255 q = 1) : d322360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d322360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33318, d322360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33319 q = 1) (hb : d322255 q = 1) : d322361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d322361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d322361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d322255 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33323 q = 1) (hb : d322255 q = 1) : d322365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d322365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86451 q ha hb
    | true =>
      simp only [d33323, d322365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33324 q = 1) (hb : d322255 q = 1) : d322366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d322366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d322366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33325 q = 1) (hb : d322255 q = 1) : d322367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d322367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33325, d322367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33360 q = 1) (hb : d322255 q = 1) : d322401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d322401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86457 q ha hb
    | true =>
      simp only [d33360, d322401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
  have h11 (q : Pattern) (ha : d265949 q = 1) (hb : d322255 q = 1) : d322402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d322402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265949, d322402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33393 q = 1) (hb : d322255 q = 1) : d322407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d322407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86458 q ha hb
    | true =>
      simp only [d33393, d322407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33394 q = 1) (hb : d322255 q = 1) : d322408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d322408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33394, d322408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265950 q = 1) (hb : d322255 q = 1) : d322409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d322409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265950, d322409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265951 q = 1) (hb : d322255 q = 1) : d322410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d322410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265951, d322410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265952 q = 1) (hb : d322255 q = 1) : d322411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d322411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265952, d322411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265953 q = 1) (hb : d322255 q = 1) : d322412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d322412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d322412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro86460 (p : Pattern) (ha : d33399 p = 1) (hb : d322255 p = 1) : d322413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d322255 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d322255 q = 1) : d322277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d322255 q = 1) : d322278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d322278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33314 q = 1) (hb : d322255 q = 1) : d322356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d322356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d322356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33399 q = 1) (hb : d322255 q = 1) : d322413 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33399, d322413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33399, d322413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro86461 (p : Pattern) (ha : d33404 p = 1) (hb : d322255 p = 1) : d322418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d322255 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d322255 q = 1) : d322277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d322277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33320 q = 1) (hb : d322255 q = 1) : d322362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d322362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d322362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33321 q = 1) (hb : d322255 q = 1) : d322363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d322363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33321, d322363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33404 q = 1) (hb : d322255 q = 1) : d322418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33404, d322418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33404, d322418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro86462 (p : Pattern) (ha : d33408 p = 1) (hb : d322255 p = 1) : d322422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d322255 q = 1) : d322395 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d322395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86456 q ha hb
    | true =>
      simp only [d33354, d322395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d322255 q = 1) : d322396 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d322396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d322396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d322255 q = 1) : d322397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d322397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d322397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d322255 q = 1) : d322398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d322398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d322398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d322255 q = 1) : d322399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d322399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d322399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33408 q = 1) (hb : d322255 q = 1) : d322422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33408, d322422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33408, d322422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86463 (p : Pattern) (ha : d33413 p = 1) (hb : d322255 p = 1) : d322425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d322255 q = 1) : d322275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86436 q ha hb
    | true =>
      simp only [d33233, d322275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d322255 q = 1) : d322276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d322276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d322255 q = 1) : d322403 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d322403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d322403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d322255 q = 1) : d322404 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d322404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d322404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d322255 q = 1) : d322405 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d322405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d322405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33413 q = 1) (hb : d322255 q = 1) : d322425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33413, d322425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33413, d322425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86464 (p : Pattern) (ha : d265958 p = 1) (hb : d322255 p = 1) : d322431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d322255 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33316 q = 1) (hb : d322255 q = 1) : d322358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d322358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86450 q ha hb
    | true =>
      simp only [d33316, d322358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33317 q = 1) (hb : d322255 q = 1) : d322359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d322359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d322359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33318 q = 1) (hb : d322255 q = 1) : d322360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d322360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33318, d322360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33319 q = 1) (hb : d322255 q = 1) : d322361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d322361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d322361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d322255 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33323 q = 1) (hb : d322255 q = 1) : d322365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d322365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86451 q ha hb
    | true =>
      simp only [d33323, d322365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33324 q = 1) (hb : d322255 q = 1) : d322366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d322366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d322366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33325 q = 1) (hb : d322255 q = 1) : d322367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d322367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33325, d322367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33360 q = 1) (hb : d322255 q = 1) : d322401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d322401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86457 q ha hb
    | true =>
      simp only [d33360, d322401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86437 q ha hb
  have h11 (q : Pattern) (ha : d265949 q = 1) (hb : d322255 q = 1) : d322402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d322402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265949, d322402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33393 q = 1) (hb : d322255 q = 1) : d322407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d322407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86458 q ha hb
    | true =>
      simp only [d33393, d322407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33394 q = 1) (hb : d322255 q = 1) : d322408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d322408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33394, d322408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265950 q = 1) (hb : d322255 q = 1) : d322409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d322409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265950, d322409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265951 q = 1) (hb : d322255 q = 1) : d322410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d322410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265951, d322410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265952 q = 1) (hb : d322255 q = 1) : d322411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d322411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265952, d322411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d322255 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d33400 q = 1) (hb : d322255 q = 1) : d322414 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33400, d322414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86460 q ha hb
    | true =>
      simp only [d33400, d322414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33401 q = 1) (hb : d322255 q = 1) : d322415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33401, d322415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33401, d322415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d33402 q = 1) (hb : d322255 q = 1) : d322416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33402, d322416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33402, d322416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d33403 q = 1) (hb : d322255 q = 1) : d322417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33403, d322417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33403, d322417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d322255 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d33405 q = 1) (hb : d322255 q = 1) : d322419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33405, d322419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86461 q ha hb
    | true =>
      simp only [d33405, d322419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d33406 q = 1) (hb : d322255 q = 1) : d322420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33406, d322420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33406, d322420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33407 q = 1) (hb : d322255 q = 1) : d322421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33407, d322421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33407, d322421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d33409 q = 1) (hb : d322255 q = 1) : d322423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d322423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86462 q ha hb
    | true =>
      simp only [d33409, d322423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86439 q ha hb
  have h27 (q : Pattern) (ha : d265954 q = 1) (hb : d322255 q = 1) : d322424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d322424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d265954, d322424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d33414 q = 1) (hb : d322255 q = 1) : d322426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d322426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86463 q ha hb
    | true =>
      simp only [d33414, d322426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d33415 q = 1) (hb : d322255 q = 1) : d322427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d322427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d33415, d322427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d265955 q = 1) (hb : d322255 q = 1) : d322428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d322428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d265955, d322428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d265956 q = 1) (hb : d322255 q = 1) : d322429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d322429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d265956, d322429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d265957 q = 1) (hb : d322255 q = 1) : d322430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d322430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265957, d322430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d265958 q = 1) (hb : d322255 q = 1) : d322431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d322431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265958, d322431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro86465 (p : Pattern) (ha : d265965 p = 1) (hb : d322255 p = 1) : d322440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33409 q = 1) (hb : d322255 q = 1) : d322423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d322423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86462 q ha hb
    | true =>
      simp only [d33409, d322423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86439 q ha hb
  have h2 (q : Pattern) (ha : d265954 q = 1) (hb : d322255 q = 1) : d322424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d322424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265954, d322424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33414 q = 1) (hb : d322255 q = 1) : d322426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d322426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86463 q ha hb
    | true =>
      simp only [d33414, d322426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33415 q = 1) (hb : d322255 q = 1) : d322427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d322427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33415, d322427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d322255 q = 1) : d322428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d322428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265955, d322428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d322255 q = 1) : d322438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d322438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d322438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d322255 q = 1) : d322439 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d322439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d322439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d322255 q = 1) : d322440 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d322440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d322440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86466 (p : Pattern) (ha : d33444 p = 1) (hb : d322255 p = 1) : d322456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33434 q = 1) (hb : d322255 q = 1) : d322446 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33434, d322446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33434, d322446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86453 q ha hb
  have h2 (q : Pattern) (ha : d33334 q = 1) (hb : d322255 q = 1) : d322375 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d322375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86453 q ha hb
    | true =>
      simp only [d33334, d322375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33435 q = 1) (hb : d322255 q = 1) : d322447 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33435, d322447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33435, d322447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33335 q = 1) (hb : d322255 q = 1) : d322376 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d322376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33335, d322376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33436 q = 1) (hb : d322255 q = 1) : d322448 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33436, d322448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33436, d322448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33437 q = 1) (hb : d322255 q = 1) : d322449 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33437, d322449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33437, d322449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33264 q = 1) (hb : d322255 q = 1) : d322306 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d322306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d322306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86434 q ha hb
  have h8 (q : Pattern) (ha : d33221 q = 1) (hb : d322255 q = 1) : d322263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86434 q ha hb
    | true =>
      simp only [d33221, d322263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33265 q = 1) (hb : d322255 q = 1) : d322307 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d322307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33265, d322307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33222 q = 1) (hb : d322255 q = 1) : d322264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33222, d322264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33266 q = 1) (hb : d322255 q = 1) : d322308 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d322308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33266, d322308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33267 q = 1) (hb : d322255 q = 1) : d322309 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d322309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33267, d322309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33438 q = 1) (hb : d322255 q = 1) : d322450 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33438, d322450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33438, d322450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33439 q = 1) (hb : d322255 q = 1) : d322451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d322451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d322451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86454 q ha hb
  have h15 (q : Pattern) (ha : d33342 q = 1) (hb : d322255 q = 1) : d322383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86454 q ha hb
    | true =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33440 q = 1) (hb : d322255 q = 1) : d322452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d322452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33440, d322452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33343 q = 1) (hb : d322255 q = 1) : d322384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33441 q = 1) (hb : d322255 q = 1) : d322453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d322453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33441, d322453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33442 q = 1) (hb : d322255 q = 1) : d322454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d322454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33442, d322454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d322255 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d33443 q = 1) (hb : d322255 q = 1) : d322455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33443, d322455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33443, d322455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d33444 q = 1) (hb : d322255 q = 1) : d322456 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33444, d322456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33444, d322456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro86467 (p : Pattern) (ha : d33450 p = 1) (hb : d322255 p = 1) : d322462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33445 q = 1) (hb : d322255 q = 1) : d322457 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d322457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86466 q ha hb
    | true =>
      simp only [d33445, d322457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86442 q ha hb
  have h2 (q : Pattern) (ha : d33446 q = 1) (hb : d322255 q = 1) : d322458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d322458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d322458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33447 q = 1) (hb : d322255 q = 1) : d322459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d322459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d322459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d322255 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33270 q = 1) (hb : d322255 q = 1) : d322312 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d322312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86442 q ha hb
    | true =>
      simp only [d33270, d322312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33271 q = 1) (hb : d322255 q = 1) : d322313 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d322313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d322313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33272 q = 1) (hb : d322255 q = 1) : d322314 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d322314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d322314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33448 q = 1) (hb : d322255 q = 1) : d322460 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d322460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33448, d322460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d322255 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33273 q = 1) (hb : d322255 q = 1) : d322315 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d322315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33273, d322315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33449 q = 1) (hb : d322255 q = 1) : d322461 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33449, d322461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33449, d322461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33450 q = 1) (hb : d322255 q = 1) : d322462 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33450, d322462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33450, d322462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro86468 (p : Pattern) (ha : d33456 p = 1) (hb : d322255 p = 1) : d322468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33451 q = 1) (hb : d322255 q = 1) : d322463 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33451, d322463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86467 q ha hb
    | true =>
      simp only [d33451, d322463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33452 q = 1) (hb : d322255 q = 1) : d322464 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33452, d322464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33452, d322464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33276 q = 1) (hb : d322255 q = 1) : d322318 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d322318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86443 q ha hb
    | true =>
      simp only [d33276, d322318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33277 q = 1) (hb : d322255 q = 1) : d322319 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d322319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d322319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33453 q = 1) (hb : d322255 q = 1) : d322465 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33453, d322465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33453, d322465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33454 q = 1) (hb : d322255 q = 1) : d322466 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33454, d322466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33454, d322466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33455 q = 1) (hb : d322255 q = 1) : d322467 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33455, d322467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33455, d322467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33456 q = 1) (hb : d322255 q = 1) : d322468 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33456, d322468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33456, d322468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86469 (p : Pattern) (ha : d33481 p = 1) (hb : d322255 p = 1) : d322474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d322255 q = 1) : d322318 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d322318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86443 q ha hb
    | true =>
      simp only [d33276, d322318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d322255 q = 1) : d322319 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d322319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d322319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33478 q = 1) (hb : d322255 q = 1) : d322471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33478, d322471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33478, d322471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33479 q = 1) (hb : d322255 q = 1) : d322472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33479, d322472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33479, d322472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33480 q = 1) (hb : d322255 q = 1) : d322473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33480, d322473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33480, d322473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33481 q = 1) (hb : d322255 q = 1) : d322474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33481, d322474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33481, d322474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86470 (p : Pattern) (ha : d265975 p = 1) (hb : d322255 p = 1) : d322480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33457 q = 1) (hb : d322255 q = 1) : d322469 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33457, d322469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86468 q ha hb
    | true =>
      simp only [d33457, d322469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86444 q ha hb
  have h2 (q : Pattern) (ha : d265971 q = 1) (hb : d322255 q = 1) : d322470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d322470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265971, d322470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33482 q = 1) (hb : d322255 q = 1) : d322475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33482, d322475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86469 q ha hb
    | true =>
      simp only [d33482, d322475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33483 q = 1) (hb : d322255 q = 1) : d322476 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33483, d322476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33483, d322476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d322255 q = 1) : d322477 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d322477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265972, d322477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d322255 q = 1) : d322478 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d322478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d322478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d322255 q = 1) : d322479 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d322479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d322479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d322255 q = 1) : d322480 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d322480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d322480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86471 (p : Pattern) (ha : d265981 p = 1) (hb : d322255 p = 1) : d322486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33304 q = 1) (hb : d322255 q = 1) : d322346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33304, d322346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33304, d322346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86447 q ha hb
  have h2 (q : Pattern) (ha : d33305 q = 1) (hb : d322255 q = 1) : d322347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33305, d322347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33305, d322347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33311 q = 1) (hb : d322255 q = 1) : d322353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86447 q ha hb
    | true =>
      simp only [d33311, d322353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86448 q ha hb
  have h4 (q : Pattern) (ha : d33312 q = 1) (hb : d322255 q = 1) : d322354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33312, d322354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33313 q = 1) (hb : d322255 q = 1) : d322355 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33313, d322355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33313, d322355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265959 q = 1) (hb : d322255 q = 1) : d322432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d322432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86459 q ha hb
    | true =>
      simp only [d265959, d322432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86464 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d322255 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33422 q = 1) (hb : d322255 q = 1) : d322434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33422, d322434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86449 q ha hb
    | true =>
      simp only [d33422, d322434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265960 q = 1) (hb : d322255 q = 1) : d322435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d322435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265960, d322435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265961 q = 1) (hb : d322255 q = 1) : d322436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d322436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265961, d322436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d265962 q = 1) (hb : d322255 q = 1) : d322437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d322437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265962, d322437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265966 q = 1) (hb : d322255 q = 1) : d322441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d322441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265966, d322441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86465 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d322255 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d265967 q = 1) (hb : d322255 q = 1) : d322442 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d322442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265967, d322442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265968 q = 1) (hb : d322255 q = 1) : d322443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d322443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265968, d322443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d265969 q = 1) (hb : d322255 q = 1) : d322444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d322444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265969, d322444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d265970 q = 1) (hb : d322255 q = 1) : d322445 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d322445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265970, d322445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265976 q = 1) (hb : d322255 q = 1) : d322481 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d322481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265976, d322481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86470 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d322255 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d265977 q = 1) (hb : d322255 q = 1) : d322482 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d322482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265977, d322482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d265978 q = 1) (hb : d322255 q = 1) : d322483 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d322483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d265978, d322483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d265979 q = 1) (hb : d322255 q = 1) : d322484 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d322484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265979, d322484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d265980 q = 1) (hb : d322255 q = 1) : d322485 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d322485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265980, d322485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d265981 q = 1) (hb : d322255 q = 1) : d322486 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d322486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265981, d322486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro86472 (p : Pattern) (ha : d265987 p = 1) (hb : d322255 p = 1) : d322492 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d322255 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d265944 q = 1) (hb : d322255 q = 1) : d322336 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265944, d322336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265944, d322336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86446 q ha hb
  have h3 (q : Pattern) (ha : d265945 q = 1) (hb : d322255 q = 1) : d322337 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265945, d322337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265945, d322337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d265946 q = 1) (hb : d322255 q = 1) : d322338 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265946, d322338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265946, d322338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265947 q = 1) (hb : d322255 q = 1) : d322339 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265947, d322339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265947, d322339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265948 q = 1) (hb : d322255 q = 1) : d322340 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265948, d322340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265948, d322340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d322255 q = 1) : d322487 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d322487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d322487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86471 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d322255 q = 1) : d322488 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d322488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d322488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d322255 q = 1) : d322489 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d322489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d322489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d322255 q = 1) : d322490 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d322490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d322490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d322255 q = 1) : d322491 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d322491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d322491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d322255 q = 1) : d322492 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d322492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265987, d322492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro86473 (p : Pattern) (ha : d33502 p = 1) (hb : d322255 p = 1) : d322495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d322255 q = 1) : d322389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d322389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86455 q ha hb
    | true =>
      simp only [d33348, d322389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d322255 q = 1) : d322390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d322390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d322390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d322255 q = 1) : d322391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d322391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d322391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d322255 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33227 q = 1) (hb : d322255 q = 1) : d322269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
    | true =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33228 q = 1) (hb : d322255 q = 1) : d322270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33229 q = 1) (hb : d322255 q = 1) : d322271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33351 q = 1) (hb : d322255 q = 1) : d322392 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d322392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d322392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33500 q = 1) (hb : d322255 q = 1) : d322493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d322493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33500, d322493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33501 q = 1) (hb : d322255 q = 1) : d322494 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33501, d322494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33501, d322494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33502 q = 1) (hb : d322255 q = 1) : d322495 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33502, d322495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33502, d322495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro86474 (p : Pattern) (ha : d33506 p = 1) (hb : d322255 p = 1) : d322499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d322255 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d322255 q = 1) : d322269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
    | true =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d322255 q = 1) : d322270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d322255 q = 1) : d322271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33500 q = 1) (hb : d322255 q = 1) : d322493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d322493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33500, d322493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33505 q = 1) (hb : d322255 q = 1) : d322498 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33505, d322498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33505, d322498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33506 q = 1) (hb : d322255 q = 1) : d322499 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33506, d322499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33506, d322499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro86475 (p : Pattern) (ha : d33512 p = 1) (hb : d322255 p = 1) : d322505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d322255 q = 1) : d322496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86473 q ha hb
    | true =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d322255 q = 1) : d322497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d322255 q = 1) : d322502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d322255 q = 1) : d322503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d322503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d322503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d322255 q = 1) : d322504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d322504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d322504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33512 q = 1) (hb : d322255 q = 1) : d322505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33512, d322505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33512, d322505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86476 (p : Pattern) (ha : d33516 p = 1) (hb : d322255 p = 1) : d322509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d322255 q = 1) : d322506 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d322255 q = 1) : d322507 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d322507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d322507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d322255 q = 1) : d322508 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d322508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d322508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33516 q = 1) (hb : d322255 q = 1) : d322509 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33516, d322509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33516, d322509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86477 (p : Pattern) (ha : d33522 p = 1) (hb : d322255 p = 1) : d322515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d322255 q = 1) : d322510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86475 q ha hb
    | true =>
      simp only [d33517, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86476 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d322255 q = 1) : d322511 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d322255 q = 1) : d322512 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d322255 q = 1) : d322513 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d322255 q = 1) : d322514 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33522 q = 1) (hb : d322255 q = 1) : d322515 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33522, d322515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33522, d322515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86478 (p : Pattern) (ha : d33525 p = 1) (hb : d322255 p = 1) : d322518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d322255 q = 1) : d322496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86473 q ha hb
    | true =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d322255 q = 1) : d322497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d322255 q = 1) : d322502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d322255 q = 1) : d322503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d322503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d322503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d322255 q = 1) : d322504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d322504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d322504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33525 q = 1) (hb : d322255 q = 1) : d322518 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33525, d322518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33525, d322518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro86479 (p : Pattern) (ha : d33526 p = 1) (hb : d322255 p = 1) : d322519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d322255 q = 1) : d322506 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d322255 q = 1) : d322507 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d322507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d322507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d322255 q = 1) : d322508 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d322508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d322508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33526 q = 1) (hb : d322255 q = 1) : d322519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33526, d322519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33526, d322519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86480 (p : Pattern) (ha : d33532 p = 1) (hb : d322255 p = 1) : d322525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d322255 q = 1) : d322510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86475 q ha hb
    | true =>
      simp only [d33517, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86476 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d322255 q = 1) : d322511 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d322255 q = 1) : d322512 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d322255 q = 1) : d322513 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d322255 q = 1) : d322514 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33527 q = 1) (hb : d322255 q = 1) : d322520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33527, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86478 q ha hb
    | true =>
      simp only [d33527, d322520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86479 q ha hb
  have h7 (q : Pattern) (ha : d33528 q = 1) (hb : d322255 q = 1) : d322521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33528, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33528, d322521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33529 q = 1) (hb : d322255 q = 1) : d322522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33529, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33529, d322522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33530 q = 1) (hb : d322255 q = 1) : d322523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33530, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33530, d322523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33531 q = 1) (hb : d322255 q = 1) : d322524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33531, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33531, d322524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33532 q = 1) (hb : d322255 q = 1) : d322525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33532, d322525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33532, d322525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro86481 (p : Pattern) (ha : d33688 p = 1) (hb : d322255 p = 1) : d322631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d322255 q = 1) : d322510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86475 q ha hb
    | true =>
      simp only [d33517, d322510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86476 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d322255 q = 1) : d322511 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d322511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d322255 q = 1) : d322512 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d322512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d322255 q = 1) : d322513 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d322513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d322255 q = 1) : d322514 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d322514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33683 q = 1) (hb : d322255 q = 1) : d322626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33683, d322626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86476 q ha hb
    | true =>
      simp only [d33683, d322626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33684 q = 1) (hb : d322255 q = 1) : d322627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33684, d322627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33684, d322627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33685 q = 1) (hb : d322255 q = 1) : d322628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33685, d322628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33685, d322628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33686 q = 1) (hb : d322255 q = 1) : d322629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33686, d322629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33686, d322629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33687 q = 1) (hb : d322255 q = 1) : d322630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33687, d322630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33687, d322630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33688 q = 1) (hb : d322255 q = 1) : d322631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33688, d322631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33688, d322631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro86482 (p : Pattern) (ha : d33694 p = 1) (hb : d322255 p = 1) : d322637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33683 q = 1) (hb : d322255 q = 1) : d322626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33683, d322626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86476 q ha hb
    | true =>
      simp only [d33683, d322626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33684 q = 1) (hb : d322255 q = 1) : d322627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33684, d322627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33684, d322627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33685 q = 1) (hb : d322255 q = 1) : d322628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33685, d322628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33685, d322628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33686 q = 1) (hb : d322255 q = 1) : d322629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33686, d322629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33686, d322629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33687 q = 1) (hb : d322255 q = 1) : d322630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33687, d322630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33687, d322630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33689 q = 1) (hb : d322255 q = 1) : d322632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33689, d322632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86479 q ha hb
    | true =>
      simp only [d33689, d322632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33690 q = 1) (hb : d322255 q = 1) : d322633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33690, d322633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33690, d322633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33691 q = 1) (hb : d322255 q = 1) : d322634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33691, d322634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33691, d322634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33692 q = 1) (hb : d322255 q = 1) : d322635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33692, d322635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33692, d322635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33693 q = 1) (hb : d322255 q = 1) : d322636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33693, d322636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33693, d322636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33694 q = 1) (hb : d322255 q = 1) : d322637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33694, d322637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33694, d322637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro86483 (p : Pattern) (ha : d33703 p = 1) (hb : d322255 p = 1) : d322646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33689 q = 1) (hb : d322255 q = 1) : d322632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33689, d322632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86479 q ha hb
    | true =>
      simp only [d33689, d322632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33690 q = 1) (hb : d322255 q = 1) : d322633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33690, d322633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33690, d322633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33691 q = 1) (hb : d322255 q = 1) : d322634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33691, d322634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33691, d322634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33692 q = 1) (hb : d322255 q = 1) : d322635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33692, d322635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33692, d322635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33693 q = 1) (hb : d322255 q = 1) : d322636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33693, d322636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33693, d322636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33703 q = 1) (hb : d322255 q = 1) : d322646 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33703, d322646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33703, d322646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86484 (p : Pattern) (ha : d33746 p = 1) (hb : d322255 p = 1) : d322689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d322255 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33270 q = 1) (hb : d322255 q = 1) : d322312 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d322312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86442 q ha hb
    | true =>
      simp only [d33270, d322312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33271 q = 1) (hb : d322255 q = 1) : d322313 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d322313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d322313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33272 q = 1) (hb : d322255 q = 1) : d322314 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d322314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d322314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33736 q = 1) (hb : d322255 q = 1) : d322679 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33736, d322679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33736, d322679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33745 q = 1) (hb : d322255 q = 1) : d322688 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33745, d322688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33745, d322688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33746 q = 1) (hb : d322255 q = 1) : d322689 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33746, d322689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33746, d322689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro86485 (p : Pattern) (ha : d33802 p = 1) (hb : d322255 p = 1) : d322712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33747 q = 1) (hb : d322255 q = 1) : d322690 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33747, d322690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86484 q ha hb
    | true =>
      simp only [d33747, d322690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33748 q = 1) (hb : d322255 q = 1) : d322691 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33748, d322691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33748, d322691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33799 q = 1) (hb : d322255 q = 1) : d322709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33799, d322709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33799, d322709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33800 q = 1) (hb : d322255 q = 1) : d322710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33800, d322710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33800, d322710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33801 q = 1) (hb : d322255 q = 1) : d322711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33801, d322711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33801, d322711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33802 q = 1) (hb : d322255 q = 1) : d322712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33802, d322712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33802, d322712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro86486 (p : Pattern) (ha : d33808 p = 1) (hb : d322255 p = 1) : d322718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33803 q = 1) (hb : d322255 q = 1) : d322713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33803, d322713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86485 q ha hb
    | true =>
      simp only [d33803, d322713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33804 q = 1) (hb : d322255 q = 1) : d322714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33804, d322714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33804, d322714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33805 q = 1) (hb : d322255 q = 1) : d322715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33805, d322715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33805, d322715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33806 q = 1) (hb : d322255 q = 1) : d322716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33806, d322716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33806, d322716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33807 q = 1) (hb : d322255 q = 1) : d322717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33807, d322717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33807, d322717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33808 q = 1) (hb : d322255 q = 1) : d322718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33808, d322718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33808, d322718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86487 (p : Pattern) (ha : d33537 p = 1) (hb : d322255 p = 1) : d322530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d322255 q = 1) : d322496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86473 q ha hb
    | true =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d322255 q = 1) : d322497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d322255 q = 1) : d322502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d322255 q = 1) : d322503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d322503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d322503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33536 q = 1) (hb : d322255 q = 1) : d322529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33536, d322529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33536, d322529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33537 q = 1) (hb : d322255 q = 1) : d322530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33537, d322530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33537, d322530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86488 (p : Pattern) (ha : d33539 p = 1) (hb : d322255 p = 1) : d322532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d322255 q = 1) : d322506 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d322255 q = 1) : d322507 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d322507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d322507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33538 q = 1) (hb : d322255 q = 1) : d322531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33538, d322531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33538, d322531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33539 q = 1) (hb : d322255 q = 1) : d322532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33539, d322532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33539, d322532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86489 (p : Pattern) (ha : d33546 p = 1) (hb : d322255 p = 1) : d322539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d322255 q = 1) : d322496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86473 q ha hb
    | true =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d322255 q = 1) : d322497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d322255 q = 1) : d322502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d322502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33544 q = 1) (hb : d322255 q = 1) : d322537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33544, d322537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33544, d322537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33545 q = 1) (hb : d322255 q = 1) : d322538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33545, d322538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33545, d322538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33546 q = 1) (hb : d322255 q = 1) : d322539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33546, d322539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33546, d322539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86490 (p : Pattern) (ha : d33549 p = 1) (hb : d322255 p = 1) : d322542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d322255 q = 1) : d322500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86474 q ha hb
    | true =>
      simp only [d33507, d322500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d322255 q = 1) : d322501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d322501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d322255 q = 1) : d322506 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d322506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33547 q = 1) (hb : d322255 q = 1) : d322540 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33547, d322540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33547, d322540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33548 q = 1) (hb : d322255 q = 1) : d322541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33548, d322541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33548, d322541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33549 q = 1) (hb : d322255 q = 1) : d322542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33549, d322542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33549, d322542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro86491 (p : Pattern) (ha : d33555 p = 1) (hb : d322255 p = 1) : d322546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d528 q = 1) (hb : d253269 q = 1) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33553 q = 1) (hb : d322254 q = 1) : d35374 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33553, d322254, d35374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33553, d322254, d35374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d1519 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1520 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1520, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33554 q = 1) (hb : d271215 q = 1) : d34367 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33554, d271215, d34367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33554, d271215, d34367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d33555 q = 1) (hb : d322255 q = 1) : d322546 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33555, d322255, d322546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33555, d322255, d322546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro86492 (p : Pattern) (ha : d33560 p = 1) (hb : d322255 p = 1) : d322550 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33326 q = 1) (hb : d322254 q = 1) : d2018 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33326, d322254, d2018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33326, d322254, d2018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d127 q = 1) : d127 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d128 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d129 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d534 q = 1) (hb : d271214 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d534, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33559 q = 1) (hb : d271215 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33559, d271215, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33559, d271215, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d33560 q = 1) (hb : d322255 q = 1) : d322550 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33560, d322255, d322550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33560, d322255, d322550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro86493 (p : Pattern) (ha : d33566 p = 1) (hb : d322255 p = 1) : d322556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33556 q = 1) (hb : d322255 q = 1) : d322547 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33556, d322547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86491 q ha hb
    | true =>
      simp only [d33556, d322547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33557 q = 1) (hb : d322255 q = 1) : d322548 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33557, d322548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33557, d322548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33328 q = 1) (hb : d322255 q = 1) : d322369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86452 q ha hb
    | true =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33329 q = 1) (hb : d322255 q = 1) : d322370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33558 q = 1) (hb : d322255 q = 1) : d322549 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33558, d322549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33558, d322549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33561 q = 1) (hb : d322255 q = 1) : d322551 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33561, d322551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86492 q ha hb
    | true =>
      simp only [d33561, d322551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33562 q = 1) (hb : d322255 q = 1) : d322552 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33562, d322552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33562, d322552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33215 q = 1) (hb : d322255 q = 1) : d322257 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86433 q ha hb
    | true =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33216 q = 1) (hb : d322255 q = 1) : d322258 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33563 q = 1) (hb : d322255 q = 1) : d322553 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33563, d322553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33563, d322553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33564 q = 1) (hb : d322255 q = 1) : d322554 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33564, d322554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33564, d322554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33565 q = 1) (hb : d322255 q = 1) : d322555 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33565, d322555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33565, d322555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33330 q = 1) (hb : d322255 q = 1) : d322371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d322255 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d33217 q = 1) (hb : d322255 q = 1) : d322259 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33331 q = 1) (hb : d322255 q = 1) : d322372 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d322372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33331, d322372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33332 q = 1) (hb : d322255 q = 1) : d322373 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d322373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33332, d322373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33566 q = 1) (hb : d322255 q = 1) : d322556 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33566, d322556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33566, d322556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro86494 (p : Pattern) (ha : d33571 p = 1) (hb : d322255 p = 1) : d322561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d322255 q = 1) : d322369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86452 q ha hb
    | true =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d322255 q = 1) : d322370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d322255 q = 1) : d322257 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86433 q ha hb
    | true =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d322255 q = 1) : d322258 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d322255 q = 1) : d322371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d322255 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33217 q = 1) (hb : d322255 q = 1) : d322259 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33331 q = 1) (hb : d322255 q = 1) : d322372 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d322372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33331, d322372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33332 q = 1) (hb : d322255 q = 1) : d322373 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d322373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33332, d322373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33339 q = 1) (hb : d322255 q = 1) : d322380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d322380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33339, d322380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33340 q = 1) (hb : d322255 q = 1) : d322381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d322381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33340, d322381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33571 q = 1) (hb : d322255 q = 1) : d322561 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33571, d322561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33571, d322561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro86495 (p : Pattern) (ha : d33579 p = 1) (hb : d322255 p = 1) : d322569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d322255 q = 1) : d322369 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86452 q ha hb
    | true =>
      simp only [d33328, d322369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d322255 q = 1) : d322370 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d322370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d322255 q = 1) : d322257 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86433 q ha hb
    | true =>
      simp only [d33215, d322257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d322255 q = 1) : d322258 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d322258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d322255 q = 1) : d322371 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d322371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33577 q = 1) (hb : d322255 q = 1) : d322567 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33577, d322567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33577, d322567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33578 q = 1) (hb : d322255 q = 1) : d322568 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33578, d322568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33578, d322568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d322255 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33217 q = 1) (hb : d322255 q = 1) : d322259 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d322259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33339 q = 1) (hb : d322255 q = 1) : d322380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d322380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33339, d322380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33340 q = 1) (hb : d322255 q = 1) : d322381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d322381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33340, d322381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33579 q = 1) (hb : d322255 q = 1) : d322569 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33579, d322569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33579, d322569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro86496 (p : Pattern) (ha : d33585 p = 1) (hb : d322255 p = 1) : d322575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33567 q = 1) (hb : d322255 q = 1) : d322557 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33567, d322557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86493 q ha hb
    | true =>
      simp only [d33567, d322557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33568 q = 1) (hb : d322255 q = 1) : d322558 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33568, d322558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33568, d322558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33569 q = 1) (hb : d322255 q = 1) : d322559 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33569, d322559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33569, d322559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33570 q = 1) (hb : d322255 q = 1) : d322560 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33570, d322560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33570, d322560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33572 q = 1) (hb : d322255 q = 1) : d322562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33572, d322562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86494 q ha hb
    | true =>
      simp only [d33572, d322562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33573 q = 1) (hb : d322255 q = 1) : d322563 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33573, d322563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33573, d322563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33574 q = 1) (hb : d322255 q = 1) : d322564 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33574, d322564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33574, d322564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33575 q = 1) (hb : d322255 q = 1) : d322565 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33575, d322565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33575, d322565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33576 q = 1) (hb : d322255 q = 1) : d322566 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33576, d322566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33576, d322566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33580 q = 1) (hb : d322255 q = 1) : d322570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33580, d322570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86495 q ha hb
    | true =>
      simp only [d33580, d322570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33581 q = 1) (hb : d322255 q = 1) : d322571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33581, d322571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33581, d322571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33582 q = 1) (hb : d322255 q = 1) : d322572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33582, d322572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33582, d322572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33583 q = 1) (hb : d322255 q = 1) : d322573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33583, d322573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33583, d322573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d33342 q = 1) (hb : d322255 q = 1) : d322383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86454 q ha hb
    | true =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33343 q = 1) (hb : d322255 q = 1) : d322384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33344 q = 1) (hb : d322255 q = 1) : d322385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d322385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d322385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33345 q = 1) (hb : d322255 q = 1) : d322386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d322386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33345, d322386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33584 q = 1) (hb : d322255 q = 1) : d322574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33584, d322574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33584, d322574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33585 q = 1) (hb : d322255 q = 1) : d322575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33585, d322575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33585, d322575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro86497 (p : Pattern) (ha : d33589 p = 1) (hb : d322255 p = 1) : d322579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33342 q = 1) (hb : d322255 q = 1) : d322383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86454 q ha hb
    | true =>
      simp only [d33342, d322383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33343 q = 1) (hb : d322255 q = 1) : d322384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33343, d322384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33344 q = 1) (hb : d322255 q = 1) : d322385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d322385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d322385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33345 q = 1) (hb : d322255 q = 1) : d322386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d322386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33345, d322386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d322255 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33346 q = 1) (hb : d322255 q = 1) : d322387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d322387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33346, d322387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d322255 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33589 q = 1) (hb : d322255 q = 1) : d322579 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33589, d322579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33589, d322579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro86498 (p : Pattern) (ha : d33595 p = 1) (hb : d322255 p = 1) : d322585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33586 q = 1) (hb : d322255 q = 1) : d322576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33586, d322576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86496 q ha hb
    | true =>
      simp only [d33586, d322576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86455 q ha hb
  have h2 (q : Pattern) (ha : d33587 q = 1) (hb : d322255 q = 1) : d322577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33587, d322577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33587, d322577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33588 q = 1) (hb : d322255 q = 1) : d322578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33588, d322578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33588, d322578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33590 q = 1) (hb : d322255 q = 1) : d322580 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33590, d322580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86455 q ha hb
    | true =>
      simp only [d33590, d322580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86497 q ha hb
  have h5 (q : Pattern) (ha : d33591 q = 1) (hb : d322255 q = 1) : d322581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33591, d322581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33591, d322581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33592 q = 1) (hb : d322255 q = 1) : d322582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33592, d322582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33592, d322582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33593 q = 1) (hb : d322255 q = 1) : d322583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33593, d322583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33593, d322583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33348 q = 1) (hb : d322255 q = 1) : d322389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d322389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86455 q ha hb
    | true =>
      simp only [d33348, d322389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
  have h9 (q : Pattern) (ha : d33349 q = 1) (hb : d322255 q = 1) : d322390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d322390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d322390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33350 q = 1) (hb : d322255 q = 1) : d322391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d322391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d322391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d322255 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d33227 q = 1) (hb : d322255 q = 1) : d322269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86435 q ha hb
    | true =>
      simp only [d33227, d322269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33228 q = 1) (hb : d322255 q = 1) : d322270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d322270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33229 q = 1) (hb : d322255 q = 1) : d322271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d322271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33351 q = 1) (hb : d322255 q = 1) : d322392 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d322392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33351, d322392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33594 q = 1) (hb : d322255 q = 1) : d322584 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33594, d322584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33594, d322584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33595 q = 1) (hb : d322255 q = 1) : d322585 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33595, d322585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33595, d322585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro86499 (p : Pattern) (ha : d33601 p = 1) (hb : d322255 p = 1) : d322591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33596 q = 1) (hb : d322255 q = 1) : d322586 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33596, d322586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86498 q ha hb
    | true =>
      simp only [d33596, d322586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33597 q = 1) (hb : d322255 q = 1) : d322587 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33597, d322587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33597, d322587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33503 q = 1) (hb : d322255 q = 1) : d322496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86473 q ha hb
    | true =>
      simp only [d33503, d322496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33504 q = 1) (hb : d322255 q = 1) : d322497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d322497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33598 q = 1) (hb : d322255 q = 1) : d322588 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33598, d322588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33598, d322588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33599 q = 1) (hb : d322255 q = 1) : d322589 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33599, d322589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33599, d322589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33600 q = 1) (hb : d322255 q = 1) : d322590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33600, d322590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33600, d322590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33601 q = 1) (hb : d322255 q = 1) : d322591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33601, d322591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33601, d322591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
