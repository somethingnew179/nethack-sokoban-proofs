import NetHack.Soko22Hazard87.AndIntroBlocks0259
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro65000 (p : Pattern) (ha : d209293 p = 1) (hb : d241366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64995 q ha hb
    | true =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64996 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209288 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64998 q ha hb
    | true =>
      simp only [d209288, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64999 q ha hb
  have h7 (q : Pattern) (ha : d209289 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209289, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209289, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209290 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209290, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209290, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209291 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209291, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209291, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209292 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209292, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209292, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209293 q = 1) (hb : d241366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209293, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209293, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65001 (p : Pattern) (ha : d209298 p = 1) (hb : d241371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64993 q ha hb
    | true =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d241344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209297 q = 1) (hb : d241370 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209297, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209297, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209298 q = 1) (hb : d241371 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209298, d241371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209298, d241371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65002 (p : Pattern) (ha : d209300 p = 1) (hb : d241373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d241348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209299 q = 1) (hb : d241372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209299, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209299, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209300 q = 1) (hb : d241373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209300, d241373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209300, d241373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65003 (p : Pattern) (ha : d209307 p = 1) (hb : d241380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64993 q ha hb
    | true =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209305 q = 1) (hb : d241378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209305, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209305, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209306 q = 1) (hb : d241379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209306, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209306, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209307 q = 1) (hb : d241380 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209307, d241380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209307, d241380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65004 (p : Pattern) (ha : d209310 p = 1) (hb : d241383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209308 q = 1) (hb : d241381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209308, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209308, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209309 q = 1) (hb : d241382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209309, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209309, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209310 q = 1) (hb : d241383 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209310, d241383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209310, d241383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65005 (p : Pattern) (ha : d27106 p = 1) (hb : d209315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64987 q ha hb
    | true =>
      simp only [d27015, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27016 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27017 q = 1) (hb : d209232 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27017, d209232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27018 q = 1) (hb : d209233 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27018, d209233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27105 q = 1) (hb : d209314 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27105, d209314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27105, d209314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27020 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
    | true =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27021 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d27022 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27022, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27023 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27023, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d27024 q = 1) (hb : d209241 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27024, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27024, d209241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27106 q = 1) (hb : d209315 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27106, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27106, d209315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro65006 (p : Pattern) (ha : d209321 p = 1) (hb : d241392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209316 q = 1) (hb : d241387 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209316, d241387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65005 q hb ha
    | true =>
      simp only [d209316, d241387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64990 q ha hb
  have h2 (q : Pattern) (ha : d209317 q = 1) (hb : d241388 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209317, d241388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209317, d241388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209318 q = 1) (hb : d241389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209318, d241389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209318, d241389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209253 q = 1) (hb : d241326 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209253, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64990 q ha hb
    | true =>
      simp only [d209253, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64991 q ha hb
  have h5 (q : Pattern) (ha : d209254 q = 1) (hb : d241327 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209254, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209254, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209255 q = 1) (hb : d241328 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209255, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209255, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209319 q = 1) (hb : d241390 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209319, d241390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209319, d241390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209257 q = 1) (hb : d241330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64991 q ha hb
    | true =>
      simp only [d209257, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64992 q ha hb
  have h9 (q : Pattern) (ha : d209258 q = 1) (hb : d241331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209259 q = 1) (hb : d241332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209260 q = 1) (hb : d241333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209260, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209320 q = 1) (hb : d241391 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209320, d241391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209320, d241391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209321 q = 1) (hb : d241392 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209321, d241392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209321, d241392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro65007 (p : Pattern) (ha : d209327 p = 1) (hb : d241398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209322 q = 1) (hb : d241393 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209322, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65006 q ha hb
    | true =>
      simp only [d209322, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209323 q = 1) (hb : d241394 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209323, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209323, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209264 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64993 q ha hb
    | true =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209265 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209324 q = 1) (hb : d241395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209324, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209324, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209325 q = 1) (hb : d241396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209325, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209325, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209326 q = 1) (hb : d241397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209326, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209326, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209327 q = 1) (hb : d241398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209327, d241398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209327, d241398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65008 (p : Pattern) (ha : d74446 p = 1) (hb : d241401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h8 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d27181 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27181, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74444 q = 1) (hb : d239849 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d74444, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74444, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d74445 q = 1) (hb : d239850 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d74445, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74445, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d74446 q = 1) (hb : d241401 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d74446, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74446, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro65009 (p : Pattern) (ha : d74453 p = 1) (hb : d241408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74447 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65008 q ha hb
    | true =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74448 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74449 q = 1) (hb : d241404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74449, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74449, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74450 q = 1) (hb : d241405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74450, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74450, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74451 q = 1) (hb : d241406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74451, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74451, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74453 q = 1) (hb : d241408 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74453, d241408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74453, d241408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65010 (p : Pattern) (ha : d209330 p = 1) (hb : d241407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27020 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
    | true =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27021 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27022 q = 1) (hb : d209239 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27022, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27022, d209239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27023 q = 1) (hb : d209240 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27023, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27023, d209240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d209245 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
    | true =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209246 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209247 q = 1) (hb : d241320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209247, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209247, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209248 q = 1) (hb : d241321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209248, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209248, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209249 q = 1) (hb : d241322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209249, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209249, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74447 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65008 q ha hb
    | true =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74448 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74449 q = 1) (hb : d241404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74449, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74449, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74450 q = 1) (hb : d241405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74450, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74450, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74451 q = 1) (hb : d241406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74451, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74451, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209330 q = 1) (hb : d241407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209330, d241407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209330, d241407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65011 (p : Pattern) (ha : d209336 p = 1) (hb : d241414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209253 q = 1) (hb : d241326 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209253, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64990 q ha hb
    | true =>
      simp only [d209253, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64991 q ha hb
  have h2 (q : Pattern) (ha : d209254 q = 1) (hb : d241327 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209254, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209254, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209255 q = 1) (hb : d241328 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209255, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209255, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209257 q = 1) (hb : d241330 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209257, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64991 q ha hb
    | true =>
      simp only [d209257, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64992 q ha hb
  have h5 (q : Pattern) (ha : d209258 q = 1) (hb : d241331 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209258, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209258, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209259 q = 1) (hb : d241332 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209259, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209259, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209260 q = 1) (hb : d241333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209260, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209260, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209331 q = 1) (hb : d241409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209331, d241409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65010 q ha hb
    | true =>
      simp only [d209331, d241409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65009 q ha hb
  have h9 (q : Pattern) (ha : d209332 q = 1) (hb : d241410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209332, d241410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209332, d241410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209333 q = 1) (hb : d241411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209333, d241411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209333, d241411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209334 q = 1) (hb : d241412 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209334, d241412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209334, d241412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209335 q = 1) (hb : d241413 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209335, d241413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209335, d241413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209336 q = 1) (hb : d241414 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209336, d241414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209336, d241414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro65012 (p : Pattern) (ha : d209342 p = 1) (hb : d241420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209337 q = 1) (hb : d241415 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209337, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65011 q ha hb
    | true =>
      simp only [d209337, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209338 q = 1) (hb : d241416 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209338, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209338, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209339 q = 1) (hb : d241417 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209339, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209339, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209340 q = 1) (hb : d241418 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209340, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209340, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209341 q = 1) (hb : d241419 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209341, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209341, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209342 q = 1) (hb : d241420 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209342, d241420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209342, d241420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65013 (p : Pattern) (ha : d209348 p = 1) (hb : d241426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209301 q = 1) (hb : d241374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209301, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65001 q ha hb
    | true =>
      simp only [d209301, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65002 q ha hb
  have h2 (q : Pattern) (ha : d209302 q = 1) (hb : d241375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209302, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209302, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209303 q = 1) (hb : d241376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209303, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209303, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209304 q = 1) (hb : d241377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209304, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209304, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209311 q = 1) (hb : d241384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209311, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65003 q ha hb
    | true =>
      simp only [d209311, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65004 q ha hb
  have h6 (q : Pattern) (ha : d209312 q = 1) (hb : d241385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209312, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209312, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209313 q = 1) (hb : d241386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209313, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209313, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209328 q = 1) (hb : d241399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209328, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65007 q ha hb
    | true =>
      simp only [d209328, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64995 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d241400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209329, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209343 q = 1) (hb : d241421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209343, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65012 q ha hb
    | true =>
      simp only [d209343, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209344 q = 1) (hb : d241422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209344, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209344, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d241423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d241424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209346, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d241425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209347, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209348 q = 1) (hb : d241426 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d241426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d241426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro65014 (p : Pattern) (ha : d209349 p = 1) (hb : d241427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64993 q ha hb
    | true =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209271 q = 1) (hb : d241344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209271, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209271, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209297 q = 1) (hb : d241370 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209297, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209297, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209349 q = 1) (hb : d241427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209349, d241427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209349, d241427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro65015 (p : Pattern) (ha : d209350 p = 1) (hb : d241428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209275 q = 1) (hb : d241348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209275, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209275, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209299 q = 1) (hb : d241372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209299, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209299, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209350 q = 1) (hb : d241428 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209350, d241428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209350, d241428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65016 (p : Pattern) (ha : d209355 p = 1) (hb : d241433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209264 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64993 q ha hb
    | true =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209265 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209270 q = 1) (hb : d241343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209270, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209305 q = 1) (hb : d241378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209305, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209305, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209306 q = 1) (hb : d241379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209306, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209306, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209355 q = 1) (hb : d241433 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209355, d241433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209355, d241433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro65017 (p : Pattern) (ha : d209356 p = 1) (hb : d241434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209268 q = 1) (hb : d241341 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64994 q ha hb
    | true =>
      simp only [d209268, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209269 q = 1) (hb : d241342 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209269, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209274 q = 1) (hb : d241347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209274, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209308 q = 1) (hb : d241381 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209308, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209308, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209309 q = 1) (hb : d241382 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209309, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209309, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209356 q = 1) (hb : d241434 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209356, d241434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209356, d241434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65018 (p : Pattern) (ha : d209360 p = 1) (hb : d241438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209322 q = 1) (hb : d241393 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209322, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65006 q ha hb
    | true =>
      simp only [d209322, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209323 q = 1) (hb : d241394 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209323, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209323, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209264 q = 1) (hb : d241337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64993 q ha hb
    | true =>
      simp only [d209264, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209265 q = 1) (hb : d241338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209265, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209324 q = 1) (hb : d241395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209324, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209324, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209325 q = 1) (hb : d241396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209325, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209325, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209326 q = 1) (hb : d241397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209326, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209326, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209360 q = 1) (hb : d241438 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209360, d241438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209360, d241438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro65019 (p : Pattern) (ha : d209363 p = 1) (hb : d241441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209337 q = 1) (hb : d241415 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209337, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65011 q ha hb
    | true =>
      simp only [d209337, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209338 q = 1) (hb : d241416 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209338, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209338, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209339 q = 1) (hb : d241417 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209339, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209339, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209340 q = 1) (hb : d241418 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209340, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209340, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209341 q = 1) (hb : d241419 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209341, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209341, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209363 q = 1) (hb : d241441 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209363, d241441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209363, d241441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65020 (p : Pattern) (ha : d209369 p = 1) (hb : d241447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209301 q = 1) (hb : d241374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209301, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65001 q ha hb
    | true =>
      simp only [d209301, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65002 q ha hb
  have h2 (q : Pattern) (ha : d209302 q = 1) (hb : d241375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209302, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209302, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209303 q = 1) (hb : d241376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209303, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209303, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209304 q = 1) (hb : d241377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209304, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209304, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209311 q = 1) (hb : d241384 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209311, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65003 q ha hb
    | true =>
      simp only [d209311, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65004 q ha hb
  have h6 (q : Pattern) (ha : d209312 q = 1) (hb : d241385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209312, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209312, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209313 q = 1) (hb : d241386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209313, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209313, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209328 q = 1) (hb : d241399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209328, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65007 q ha hb
    | true =>
      simp only [d209328, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64995 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d209329 q = 1) (hb : d241400 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209329, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d209343 q = 1) (hb : d241421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209343, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65012 q ha hb
    | true =>
      simp only [d209343, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209344 q = 1) (hb : d241422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209344, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209344, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209345 q = 1) (hb : d241423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209345, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209346 q = 1) (hb : d241424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209346, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209347 q = 1) (hb : d241425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209347, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209351 q = 1) (hb : d241429 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209351, d241429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65014 q ha hb
    | true =>
      simp only [d209351, d241429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65015 q ha hb
  have h17 (q : Pattern) (ha : d209352 q = 1) (hb : d241430 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209352, d241430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209352, d241430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209353 q = 1) (hb : d241431 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209353, d241431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209353, d241431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d209354 q = 1) (hb : d241432 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209354, d241432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209354, d241432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209357 q = 1) (hb : d241435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209357, d241435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65016 q ha hb
    | true =>
      simp only [d209357, d241435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65017 q ha hb
  have h21 (q : Pattern) (ha : d209358 q = 1) (hb : d241436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209358, d241436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209358, d241436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d209359 q = 1) (hb : d241437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209359, d241437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209359, d241437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209361 q = 1) (hb : d241439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209361, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65018 q ha hb
    | true =>
      simp only [d209361, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64998 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d209362 q = 1) (hb : d241440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d209362, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d209364 q = 1) (hb : d241442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209364, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65019 q ha hb
    | true =>
      simp only [d209364, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d209365 q = 1) (hb : d241443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209365, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d209365, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d209366 q = 1) (hb : d241444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d209366, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d209367 q = 1) (hb : d241445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d241445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d209367, d241445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d209368 q = 1) (hb : d241446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d241446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209368, d241446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d209369 q = 1) (hb : d241447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d241447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209369, d241447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro65021 (p : Pattern) (ha : d209376 p = 1) (hb : d241454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209278 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64995 q ha hb
    | true =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64996 q ha hb
  have h2 (q : Pattern) (ha : d209279 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209279, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209279, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209280 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209280, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209280, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209281 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209281, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209281, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209282 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209282, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209282, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209371 q = 1) (hb : d241449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209371, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64996 q ha hb
    | true =>
      simp only [d209371, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209372 q = 1) (hb : d241450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209372, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209372, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209373 q = 1) (hb : d241451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209373, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209373, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209374 q = 1) (hb : d241452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209374, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209374, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209375 q = 1) (hb : d241453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209375, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209375, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209376 q = 1) (hb : d241454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209376, d241454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209376, d241454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65022 (p : Pattern) (ha : d209382 p = 1) (hb : d241460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209371 q = 1) (hb : d241449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209371, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64996 q ha hb
    | true =>
      simp only [d209371, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209372 q = 1) (hb : d241450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209372, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209372, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209373 q = 1) (hb : d241451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209373, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209373, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209374 q = 1) (hb : d241452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209374, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209374, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209375 q = 1) (hb : d241453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209375, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209375, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209377 q = 1) (hb : d241455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209377, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64999 q ha hb
    | true =>
      simp only [d209377, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209378 q = 1) (hb : d241456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209378, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209378, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209379 q = 1) (hb : d241457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209379, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209379, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209380 q = 1) (hb : d241458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209380, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209380, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209381 q = 1) (hb : d241459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209381, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209381, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209382 q = 1) (hb : d241460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209382, d241460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209382, d241460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65023 (p : Pattern) (ha : d209389 p = 1) (hb : d241467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209361 q = 1) (hb : d241439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209361, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65018 q ha hb
    | true =>
      simp only [d209361, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64998 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d241440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209362, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209364 q = 1) (hb : d241442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209364, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65019 q ha hb
    | true =>
      simp only [d209364, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209365 q = 1) (hb : d241443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209365, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209365, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209366 q = 1) (hb : d241444 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209387 q = 1) (hb : d241465 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d241465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d241465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209388 q = 1) (hb : d241466 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d241466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d241466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209389 q = 1) (hb : d241467 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d241467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d241467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro65024 (p : Pattern) (ha : d209391 p = 1) (hb : d241469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209377 q = 1) (hb : d241455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209377, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64999 q ha hb
    | true =>
      simp only [d209377, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209378 q = 1) (hb : d241456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209378, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209378, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209379 q = 1) (hb : d241457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209379, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209379, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209380 q = 1) (hb : d241458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209380, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209380, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209381 q = 1) (hb : d241459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209381, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209381, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209391 q = 1) (hb : d241469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209391, d241469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209391, d241469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65025 (p : Pattern) (ha : d27277 p = 1) (hb : d209407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27267 q = 1) (hb : d209397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27267, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64987 q ha hb
  have h3 (q : Pattern) (ha : d27015 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64987 q ha hb
    | true =>
      simp only [d27015, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27268 q = 1) (hb : d209398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27268, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27016 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27016, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27269 q = 1) (hb : d209399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27269, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27270 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27270, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27271 q = 1) (hb : d209401 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27271, d209401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27271, d209401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27272 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
  have h10 (q : Pattern) (ha : d27020 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
    | true =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d27273 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27021 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d27274 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27275 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d27276 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27276, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27276, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27277 q = 1) (hb : d209407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27277, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27277, d209407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro65026 (p : Pattern) (ha : d209413 p = 1) (hb : d241480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d209397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d209397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64987 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d209230 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64987 q ha hb
    | true =>
      simp only [d27015, d209230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d209398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d209398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d209231 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d209231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d209399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d209399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d209400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d209400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27272 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
  have h8 (q : Pattern) (ha : d27020 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
    | true =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27273 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27021 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27274 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27275 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d27276 q = 1) (hb : d209406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27276, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27276, d209406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209408 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
  have h15 (q : Pattern) (ha : d209245 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
    | true =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209409 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209246 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d209410 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d209411 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d209412 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209412, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d209412, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d209413 q = 1) (hb : d241480 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209413, d241480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d209413, d241480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro65027 (p : Pattern) (ha : d209418 p = 1) (hb : d241485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
    | true =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209408 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
  have h8 (q : Pattern) (ha : d209245 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
    | true =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209409 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209246 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209410 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209411 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209412 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209412, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209412, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209417 q = 1) (hb : d241484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209417, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209417, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209418 q = 1) (hb : d241485 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209418, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209418, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65028 (p : Pattern) (ha : d209423 p = 1) (hb : d241490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209408 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
  have h2 (q : Pattern) (ha : d209245 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
    | true =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209409 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209246 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209410 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209411 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209417 q = 1) (hb : d241484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209417, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209417, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d2361 q = 1) (hb : d53526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
  have h9 (q : Pattern) (ha : d2080 q = 1) (hb : d53359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro271 q ha hb
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2362 q = 1) (hb : d53527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2081 q = 1) (hb : d53360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2363 q = 1) (hb : d53528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2364 q = 1) (hb : d53529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d2365 q = 1) (hb : d53530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d209423 q = 1) (hb : d241490 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209423, d241490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209423, d241490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro65029 (p : Pattern) (ha : d209429 p = 1) (hb : d241496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209414 q = 1) (hb : d241481 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209414, d241481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65025 q hb ha
    | true =>
      simp only [d209414, d241481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65026 q ha hb
  have h2 (q : Pattern) (ha : d209415 q = 1) (hb : d241482 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209415, d241482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209415, d241482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209416 q = 1) (hb : d241483 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209416, d241483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209416, d241483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209419 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209419, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65026 q ha hb
    | true =>
      simp only [d209419, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
  have h5 (q : Pattern) (ha : d209420 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209420, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209420, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209421 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209421, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209421, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209422 q = 1) (hb : d241489 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209422, d241489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209422, d241489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209424 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
    | true =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65028 q ha hb
  have h9 (q : Pattern) (ha : d209425 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209426 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209427 q = 1) (hb : d241494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209427, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209428 q = 1) (hb : d241495 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209428, d241495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209428, d241495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209429 q = 1) (hb : d241496 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209429, d241496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209429, d241496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro65030 (p : Pattern) (ha : d209434 p = 1) (hb : d241501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209419 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209419, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65026 q ha hb
    | true =>
      simp only [d209419, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
  have h2 (q : Pattern) (ha : d209420 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209420, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209420, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209421 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209421, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209421, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209424 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
    | true =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65028 q ha hb
  have h5 (q : Pattern) (ha : d209425 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209426 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209427 q = 1) (hb : d241494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209427, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209432 q = 1) (hb : d241499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209432, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209432, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209433 q = 1) (hb : d241500 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209433, d241500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209433, d241500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209434 q = 1) (hb : d241501 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209434, d241501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209434, d241501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro65031 (p : Pattern) (ha : d209440 p = 1) (hb : d241507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209430 q = 1) (hb : d241497 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209430, d241497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65029 q ha hb
    | true =>
      simp only [d209430, d241497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209431 q = 1) (hb : d241498 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209431, d241498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209431, d241498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209435 q = 1) (hb : d241502 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209435, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65030 q ha hb
    | true =>
      simp only [d209435, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209436 q = 1) (hb : d241503 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209436, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209436, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209437 q = 1) (hb : d241504 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209437, d241504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209437, d241504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209438 q = 1) (hb : d241505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209438, d241505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209438, d241505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209439 q = 1) (hb : d241506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209439, d241506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209439, d241506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209440 q = 1) (hb : d241507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209440, d241507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209440, d241507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro65032 (p : Pattern) (ha : d209442 p = 1) (hb : d241509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209424 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
    | true =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65028 q ha hb
  have h2 (q : Pattern) (ha : d209425 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209426 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209432 q = 1) (hb : d241499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209432, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209432, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209441 q = 1) (hb : d241508 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209441, d241508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209441, d241508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209442 q = 1) (hb : d241509 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209442, d241509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209442, d241509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65033 (p : Pattern) (ha : d209448 p = 1) (hb : d241515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209435 q = 1) (hb : d241502 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209435, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65030 q ha hb
    | true =>
      simp only [d209435, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209436 q = 1) (hb : d241503 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209436, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209436, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209443 q = 1) (hb : d241510 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209443, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65032 q ha hb
    | true =>
      simp only [d209443, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209444 q = 1) (hb : d241511 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209444, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209444, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209445 q = 1) (hb : d241512 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209445, d241512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209445, d241512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209446 q = 1) (hb : d241513 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209446, d241513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209446, d241513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d209447 q = 1) (hb : d241514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209447, d241514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209447, d241514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d209448 q = 1) (hb : d241515 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209448, d241515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209448, d241515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro65034 (p : Pattern) (ha : d74497 p = 1) (hb : d241524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74491 q = 1) (hb : d241518 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74491, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74491, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65008 q ha hb
  have h2 (q : Pattern) (ha : d74447 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65008 q ha hb
    | true =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74492 q = 1) (hb : d241519 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74492, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74492, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74448 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74493 q = 1) (hb : d241520 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74493, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74493, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74494 q = 1) (hb : d241521 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74494, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74494, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d74495 q = 1) (hb : d241522 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74495, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74495, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d74497 q = 1) (hb : d241524 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74497, d241524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74497, d241524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro65035 (p : Pattern) (ha : d209456 p = 1) (hb : d241523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27272 q = 1) (hb : d209402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27272, d209402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
  have h2 (q : Pattern) (ha : d27020 q = 1) (hb : d209237 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64988 q ha hb
    | true =>
      simp only [d27020, d209237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27273 q = 1) (hb : d209403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27273, d209403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27021 q = 1) (hb : d209238 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27021, d209238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27274 q = 1) (hb : d209404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27274, d209404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27275 q = 1) (hb : d209405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27275, d209405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d209408 q = 1) (hb : d241475 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209408, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
  have h8 (q : Pattern) (ha : d209245 q = 1) (hb : d241318 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64989 q ha hb
    | true =>
      simp only [d209245, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d209409 q = 1) (hb : d241476 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209409, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209246 q = 1) (hb : d241319 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209246, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d209410 q = 1) (hb : d241477 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209410, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d209411 q = 1) (hb : d241478 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209411, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d209412 q = 1) (hb : d241479 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d209412, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d209412, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74491 q = 1) (hb : d241518 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74491, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74491, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65008 q ha hb
  have h15 (q : Pattern) (ha : d74447 q = 1) (hb : d241402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65008 q ha hb
    | true =>
      simp only [d74447, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74492 q = 1) (hb : d241519 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74492, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74492, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74448 q = 1) (hb : d241403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74448, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74493 q = 1) (hb : d241520 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74493, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74493, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74494 q = 1) (hb : d241521 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74494, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74494, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74495 q = 1) (hb : d241522 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74495, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74495, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209456 q = 1) (hb : d241523 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d209456, d241523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209456, d241523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro65036 (p : Pattern) (ha : d209462 p = 1) (hb : d241530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209419 q = 1) (hb : d241486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209419, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65026 q ha hb
    | true =>
      simp only [d209419, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
  have h2 (q : Pattern) (ha : d209420 q = 1) (hb : d241487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209420, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209420, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209421 q = 1) (hb : d241488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209421, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209421, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209424 q = 1) (hb : d241491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65027 q ha hb
    | true =>
      simp only [d209424, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65028 q ha hb
  have h5 (q : Pattern) (ha : d209425 q = 1) (hb : d241492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209425, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209426 q = 1) (hb : d241493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209426, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209427 q = 1) (hb : d241494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209427, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209427, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209457 q = 1) (hb : d241525 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d209457, d241525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65035 q ha hb
    | true =>
      simp only [d209457, d241525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65034 q ha hb
  have h9 (q : Pattern) (ha : d209458 q = 1) (hb : d241526 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d209458, d241526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209458, d241526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209459 q = 1) (hb : d241527 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d209459, d241527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209459, d241527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209460 q = 1) (hb : d241528 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d209460, d241528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209460, d241528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d209461 q = 1) (hb : d241529 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d209461, d241529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209461, d241529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209462 q = 1) (hb : d241530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d209462, d241530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209462, d241530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro65037 (p : Pattern) (ha : d209468 p = 1) (hb : d241536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209463 q = 1) (hb : d241531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209463, d241531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65036 q ha hb
    | true =>
      simp only [d209463, d241531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209464 q = 1) (hb : d241532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209464, d241532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209464, d241532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209465 q = 1) (hb : d241533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209465, d241533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209465, d241533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209466 q = 1) (hb : d241534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209466, d241534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209466, d241534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209467 q = 1) (hb : d241535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209467, d241535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209467, d241535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209468 q = 1) (hb : d241536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209468, d241536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209468, d241536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65038 (p : Pattern) (ha : d209474 p = 1) (hb : d241542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209449 q = 1) (hb : d241516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209449, d241516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65031 q ha hb
    | true =>
      simp only [d209449, d241516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65033 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d241517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d241517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209455, d241517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d209469 q = 1) (hb : d241537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209469, d241537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65037 q ha hb
    | true =>
      simp only [d209469, d241537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209470 q = 1) (hb : d241538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209470, d241538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209470, d241538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209471 q = 1) (hb : d241539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d241539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d241539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209472 q = 1) (hb : d241540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d241540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d241540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209473 q = 1) (hb : d241541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d241541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d241541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209474 q = 1) (hb : d241542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d241542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d241542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro65039 (p : Pattern) (ha : d209453 p = 1) (hb : d241547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209443 q = 1) (hb : d241510 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d209443, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65032 q ha hb
    | true =>
      simp only [d209443, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209444 q = 1) (hb : d241511 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d209444, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209444, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209450 q = 1) (hb : d241544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d209450, d241544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209450, d241544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209451 q = 1) (hb : d241545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d209451, d241545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209451, d241545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209452 q = 1) (hb : d241546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d209452, d241546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209452, d241546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209453 q = 1) (hb : d241547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d209453, d241547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209453, d241547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65040 (p : Pattern) (ha : d209481 p = 1) (hb : d241553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209476 q = 1) (hb : d241548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209476, d241548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65039 q ha hb
    | true =>
      simp only [d209476, d241548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209477 q = 1) (hb : d241549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209477, d241549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209477, d241549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209478 q = 1) (hb : d241550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209478, d241550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209478, d241550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209479 q = 1) (hb : d241551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209479, d241551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209479, d241551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209480 q = 1) (hb : d241552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209480, d241552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209480, d241552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209481 q = 1) (hb : d241553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209481, d241553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209481, d241553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65041 (p : Pattern) (ha : d209487 p = 1) (hb : d241559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209284 q = 1) (hb : d241357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209284, d241357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209284, d241357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64997 q ha hb
  have h2 (q : Pattern) (ha : d209285 q = 1) (hb : d241358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209285, d241358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209285, d241358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209294 q = 1) (hb : d241367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209294, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64997 q ha hb
    | true =>
      simp only [d209294, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65000 q ha hb
  have h4 (q : Pattern) (ha : d209295 q = 1) (hb : d241368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209295, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209295, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209296 q = 1) (hb : d241369 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209296, d241369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209296, d241369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209370 q = 1) (hb : d241448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d241448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65013 q ha hb
    | true =>
      simp only [d209370, d241448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65020 q ha hb
  have h7 (q : Pattern) (ha : d209383 q = 1) (hb : d241461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209383, d241461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65021 q ha hb
    | true =>
      simp only [d209383, d241461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65022 q ha hb
  have h8 (q : Pattern) (ha : d209384 q = 1) (hb : d241462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d241462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209384, d241462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209385 q = 1) (hb : d241463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d241463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209385, d241463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d209386 q = 1) (hb : d241464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d241464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209386, d241464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209390 q = 1) (hb : d241468 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d241468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209390, d241468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65023 q ha hb
  have h12 (q : Pattern) (ha : d209392 q = 1) (hb : d241470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209392, d241470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209392, d241470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65024 q ha hb
  have h13 (q : Pattern) (ha : d209393 q = 1) (hb : d241471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d241471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d209393, d241471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209394 q = 1) (hb : d241472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d241472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209394, d241472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d209395 q = 1) (hb : d241473 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d241473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d209395, d241473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d209396 q = 1) (hb : d241474 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d241474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209396, d241474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209475 q = 1) (hb : d241543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d241543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209475, d241543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65038 q ha hb
  have h18 (q : Pattern) (ha : d209482 q = 1) (hb : d241554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209482, d241554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209482, d241554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65040 q ha hb
  have h19 (q : Pattern) (ha : d209483 q = 1) (hb : d241555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d241555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209483, d241555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d209484 q = 1) (hb : d241556 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d241556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d209484, d241556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d209485 q = 1) (hb : d241557 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d241557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d209485, d241557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d209486 q = 1) (hb : d241558 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d241558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d209486, d241558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d209487 q = 1) (hb : d241559 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d241559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209487, d241559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro65042 (p : Pattern) (ha : d209493 p = 1) (hb : d241565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d241560 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d241560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d241560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65041 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d241561 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d241561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d241561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d241562 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d241562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d241562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d241563 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d241563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d241563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d241564 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d241564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d241564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d241565 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d241565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d241565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65043 (p : Pattern) (ha : d209499 p = 1) (hb : d241571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d240587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d240587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64786 q ha hb
    | true =>
      simp only [d208438, d240587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64827 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d240806 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d240806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d240806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64872 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d240807 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d240807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d240807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d241057 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d241057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d241057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64929 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d241058 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d241058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d241058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d241059 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d241059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d241059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d241313 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d241313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d241313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64986 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d241314 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d241314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d241314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d241315 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d241315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d241315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d241316 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d241316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d241316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d241566 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d241566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d241566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65042 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d241567 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d241567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d241567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d241568 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d241568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d241568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d241569 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d241569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d241569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d241570 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d241570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d241570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d241571 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d241571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d241571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro65044 (p : Pattern) (ha : d209505 p = 1) (hb : d241577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d241572 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d241572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65043 q ha hb
    | true =>
      simp only [d209500, d241572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d241573 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d241573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d241573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d241574 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d241574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d241574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d241575 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d241575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d241575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d241576 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d241576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d241576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d241577 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d241577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d241577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65045 (p : Pattern) (ha : d209511 p = 1) (hb : d241583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d241578 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d241578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65044 q ha hb
    | true =>
      simp only [d209506, d241578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d241579 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d241579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d241579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d241580 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d241580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d241580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d241581 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d241581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d241581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d241582 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d241582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d241582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d241583 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d241583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d241583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65046 (p : Pattern) (ha : d209517 p = 1) (hb : d241589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d241584 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d241584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65045 q ha hb
    | true =>
      simp only [d209512, d241584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d241585 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d241585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d241585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d241586 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d241586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d241586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d241587 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d241587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d241587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d241588 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d241588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d241588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d241589 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d241589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d241589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65047 (p : Pattern) (ha : d209523 p = 1) (hb : d241595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d241590 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d241590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65046 q ha hb
    | true =>
      simp only [d209518, d241590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d241591 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d241591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d241591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d241592 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d241592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d241592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d241593 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d241593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d241593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d241594 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d241594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d241594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d241595 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d241595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d241595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65048 (p : Pattern) (ha : d209529 p = 1) (hb : d241601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d241596 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d241596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65047 q ha hb
    | true =>
      simp only [d209524, d241596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d241597 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d241597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d241597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d241598 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d241598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d241598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d241599 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d241599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d241599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d241600 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d241600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d241600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d241601 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d241601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d241601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65049 (p : Pattern) (ha : d209535 p = 1) (hb : d241607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d241602 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d241602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65048 q ha hb
    | true =>
      simp only [d209530, d241602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d241603 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d241603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d241603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d241604 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d241604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d241604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d241605 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d241605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d241605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d241606 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d241606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d241606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d241607 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d241607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d241607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65050 (p : Pattern) (ha : d209541 p = 1) (hb : d241613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d241608 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d241608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65049 q ha hb
    | true =>
      simp only [d209536, d241608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d241609 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d241609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d241609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d241610 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d241610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d241610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d241611 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d241611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d241611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d241612 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d241612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d241612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d241613 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d241613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d241613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65051 (p : Pattern) (ha : d208034 p = 1) (hb : d245682 p = 1) : d241616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d208034 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d208034 q = 1) : d240231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64441 q ha hb
    | true =>
      simp only [d25130, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d208034 q = 1) : d240285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25191 q = 1) (hb : d208034 q = 1) : d240286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25192 q = 1) (hb : d208034 q = 1) : d240287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25193 q = 1) (hb : d208034 q = 1) : d240288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245682 q = 1) : d241616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245682, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245682, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro65052 (p : Pattern) (ha : d208034 p = 1) (hb : d245692 p = 1) : d241626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d208034 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d208034 q = 1) : d240261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64446 q ha hb
    | true =>
      simp only [d25166, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245688 q = 1) : d241622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245688, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245688, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245689 q = 1) : d241623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245689, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245689, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245690 q = 1) : d241624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245690, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245690, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245691 q = 1) : d241625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245691, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245691, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245692 q = 1) : d241626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245692, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245692, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro65053 (p : Pattern) (ha : d208034 p = 1) (hb : d245698 p = 1) : d241632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d208034 q = 1) : d240290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64449 q ha hb
    | true =>
      simp only [d25195, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64450 q ha hb
  have h2 (q : Pattern) (ha : d25196 q = 1) (hb : d208034 q = 1) : d240291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245680 q = 1) : d241614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245680, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245680, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245681 q = 1) : d241615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245681, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245681, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245683 q = 1) : d241617 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245683, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245683, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65051 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245684 q = 1) : d241618 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245684, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245684, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245685 q = 1) : d241619 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245685, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245685, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245686 q = 1) : d241620 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245686, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245686, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245687 q = 1) : d241621 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245687, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245687, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245693 q = 1) : d241627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245693, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245693, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65052 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245694 q = 1) : d241628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245694, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245694, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245695 q = 1) : d241629 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245695, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245695, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245696 q = 1) : d241630 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245696, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245696, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245697 q = 1) : d241631 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245697, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245697, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245698 q = 1) : d241632 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245698, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245698, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65054 (p : Pattern) (ha : d208034 p = 1) (hb : d245704 p = 1) : d241638 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d208034 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245699 q = 1) : d241633 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245699, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245699, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65053 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245700 q = 1) : d241634 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245700, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245700, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245701 q = 1) : d241635 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245701, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245701, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245702 q = 1) : d241636 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245702, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245702, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245703 q = 1) : d241637 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245703, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245703, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245704 q = 1) : d241638 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245704, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245704, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro65055 (p : Pattern) (ha : d208034 p = 1) (hb : d245707 p = 1) : d241641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25402 q = 1) (hb : d208034 q = 1) : d240427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64478 q ha hb
    | true =>
      simp only [d25402, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64479 q ha hb
  have h2 (q : Pattern) (ha : d25403 q = 1) (hb : d208034 q = 1) : d240428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25404 q = 1) (hb : d208034 q = 1) : d240429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25404, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25405 q = 1) (hb : d208034 q = 1) : d240430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25406 q = 1) (hb : d208034 q = 1) : d240431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245707 q = 1) : d241641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245707, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245707, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro65056 (p : Pattern) (ha : d208034 p = 1) (hb : d245718 p = 1) : d241652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245713 q = 1) : d241647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245713, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64510 q hb ha
    | true =>
      simp only [d245713, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64485 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245714 q = 1) : d241648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245714, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245714, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245715 q = 1) : d241649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245715, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245715, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245716 q = 1) : d241650 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245716, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245716, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245717 q = 1) : d241651 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245717, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245717, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245718 q = 1) : d241652 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245718, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245718, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65057 (p : Pattern) (ha : d208034 p = 1) (hb : d245724 p = 1) : d241658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25408 q = 1) (hb : d208034 q = 1) : d240433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64477 q ha hb
    | true =>
      simp only [d25408, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64480 q ha hb
  have h2 (q : Pattern) (ha : d25409 q = 1) (hb : d208034 q = 1) : d240434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25409, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245705 q = 1) : d241639 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245705, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245705, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245706 q = 1) : d241640 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245706, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245706, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245708 q = 1) : d241642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245708, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245708, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65055 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245709 q = 1) : d241643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245709, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245709, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245710 q = 1) : d241644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245710, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245710, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245711 q = 1) : d241645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245711, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245711, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245712 q = 1) : d241646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245712, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245712, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245719 q = 1) : d241653 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245719, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245719, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65056 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245720 q = 1) : d241654 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245720, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245720, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245721 q = 1) : d241655 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245721, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245721, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245722 q = 1) : d241656 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245722, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245722, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245723 q = 1) : d241657 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245723, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245723, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245724 q = 1) : d241658 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245724, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245724, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65058 (p : Pattern) (ha : d208034 p = 1) (hb : d245730 p = 1) : d241664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245725 q = 1) : d241659 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245725, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245725, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65057 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245726 q = 1) : d241660 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245726, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245726, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245727 q = 1) : d241661 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245727, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245727, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245728 q = 1) : d241662 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245728, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245728, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245729 q = 1) : d241663 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245729, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245729, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245730 q = 1) : d241664 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245730, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245730, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65059 (p : Pattern) (ha : d208034 p = 1) (hb : d245734 p = 1) : d241668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25735 q = 1) (hb : d208034 q = 1) : d240625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64524 q ha hb
    | true =>
      simp only [d25735, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64525 q ha hb
  have h2 (q : Pattern) (ha : d25736 q = 1) (hb : d208034 q = 1) : d240626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25737 q = 1) (hb : d208034 q = 1) : d240627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25737, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25738 q = 1) (hb : d208034 q = 1) : d240628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25739 q = 1) (hb : d208034 q = 1) : d240629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245734 q = 1) : d241668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245734, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245734, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro65060 (p : Pattern) (ha : d208034 p = 1) (hb : d245745 p = 1) : d241679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245740 q = 1) : d241674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245740, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64561 q hb ha
    | true =>
      simp only [d245740, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64533 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245741 q = 1) : d241675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245741, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245741, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245742 q = 1) : d241676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245742, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245742, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245743 q = 1) : d241677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245743, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245743, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245744 q = 1) : d241678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245744, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245744, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245745 q = 1) : d241679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245745, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245745, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65061 (p : Pattern) (ha : d208034 p = 1) (hb : d245751 p = 1) : d241685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25741 q = 1) (hb : d208034 q = 1) : d240631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64523 q ha hb
    | true =>
      simp only [d25741, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64526 q ha hb
  have h2 (q : Pattern) (ha : d25742 q = 1) (hb : d208034 q = 1) : d240632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25742, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245732 q = 1) : d241666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245732, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245732, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245733 q = 1) : d241667 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245733, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245733, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245735 q = 1) : d241669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245735, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245735, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65059 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245736 q = 1) : d241670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245736, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245736, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245737 q = 1) : d241671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245737, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245737, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245738 q = 1) : d241672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245738, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245738, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245739 q = 1) : d241673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245739, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245739, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245746 q = 1) : d241680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245746, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245746, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65060 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245747 q = 1) : d241681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245747, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245747, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245748 q = 1) : d241682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245748, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245748, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245749 q = 1) : d241683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245749, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245749, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245750 q = 1) : d241684 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245750, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245750, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245751 q = 1) : d241685 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245751, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245751, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65062 (p : Pattern) (ha : d208034 p = 1) (hb : d245757 p = 1) : d241691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245752 q = 1) : d241686 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245752, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245752, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65061 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245753 q = 1) : d241687 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245753, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245753, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245754 q = 1) : d241688 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245754, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245754, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245755 q = 1) : d241689 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245755, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245755, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245756 q = 1) : d241690 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245756, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245756, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245757 q = 1) : d241691 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245757, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245757, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65063 (p : Pattern) (ha : d208034 p = 1) (hb : d245762 p = 1) : d241696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26159 q = 1) (hb : d208034 q = 1) : d240852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64579 q ha hb
    | true =>
      simp only [d26159, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64580 q ha hb
  have h2 (q : Pattern) (ha : d26160 q = 1) (hb : d208034 q = 1) : d240853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26161 q = 1) (hb : d208034 q = 1) : d240854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26161, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26162 q = 1) (hb : d208034 q = 1) : d240855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26163 q = 1) (hb : d208034 q = 1) : d240856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245762 q = 1) : d241696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245762, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245762, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro65064 (p : Pattern) (ha : d208034 p = 1) (hb : d245773 p = 1) : d241707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245768 q = 1) : d241702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245768, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64618 q hb ha
    | true =>
      simp only [d245768, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64588 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245769 q = 1) : d241703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245769, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245769, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245770 q = 1) : d241704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245770, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245770, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245771 q = 1) : d241705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245771, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245771, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245772 q = 1) : d241706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245772, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245772, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245773 q = 1) : d241707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245773, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245773, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65065 (p : Pattern) (ha : d208034 p = 1) (hb : d245779 p = 1) : d241713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26165 q = 1) (hb : d208034 q = 1) : d240858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64578 q ha hb
    | true =>
      simp only [d26165, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64581 q ha hb
  have h2 (q : Pattern) (ha : d26166 q = 1) (hb : d208034 q = 1) : d240859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26166, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245760 q = 1) : d241694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245760, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245760, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245761 q = 1) : d241695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245761, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245761, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245763 q = 1) : d241697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245763, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245763, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65063 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245764 q = 1) : d241698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245764, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245764, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245765 q = 1) : d241699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245765, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245765, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245766 q = 1) : d241700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245766, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245766, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245767 q = 1) : d241701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245767, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245767, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245774 q = 1) : d241708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245774, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245774, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65064 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245775 q = 1) : d241709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245775, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245775, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245776 q = 1) : d241710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245776, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245776, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245777 q = 1) : d241711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245777, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245777, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245778 q = 1) : d241712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245778, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245778, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245779 q = 1) : d241713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245779, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245779, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65066 (p : Pattern) (ha : d208034 p = 1) (hb : d245785 p = 1) : d241719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245780 q = 1) : d241714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245780, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245780, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65065 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245781 q = 1) : d241715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245781, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245781, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245782 q = 1) : d241716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245782, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245782, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245783 q = 1) : d241717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245783, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245783, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245784 q = 1) : d241718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245784, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245784, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245785 q = 1) : d241719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245785, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245785, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65067 (p : Pattern) (ha : d208034 p = 1) (hb : d245791 p = 1) : d241725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26626 q = 1) (hb : d208034 q = 1) : d241104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64638 q ha hb
    | true =>
      simp only [d26626, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64639 q ha hb
  have h2 (q : Pattern) (ha : d26627 q = 1) (hb : d208034 q = 1) : d241105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26628 q = 1) (hb : d208034 q = 1) : d241106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26628, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26629 q = 1) (hb : d208034 q = 1) : d241107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26630 q = 1) (hb : d208034 q = 1) : d241108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245791 q = 1) : d241725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245791, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245791, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro65068 (p : Pattern) (ha : d208034 p = 1) (hb : d245802 p = 1) : d241736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245797 q = 1) : d241731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245797, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64677 q hb ha
    | true =>
      simp only [d245797, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64647 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245798 q = 1) : d241732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245798, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245798, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245799 q = 1) : d241733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245799, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245799, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245800 q = 1) : d241734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245800, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245800, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245801 q = 1) : d241735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245801, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245801, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245802 q = 1) : d241736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245802, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245802, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65069 (p : Pattern) (ha : d208034 p = 1) (hb : d245808 p = 1) : d241742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26632 q = 1) (hb : d208034 q = 1) : d241110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64637 q ha hb
    | true =>
      simp only [d26632, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64640 q ha hb
  have h2 (q : Pattern) (ha : d26633 q = 1) (hb : d208034 q = 1) : d241111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26633, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245789 q = 1) : d241723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245789, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245789, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245790 q = 1) : d241724 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245790, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245790, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245792 q = 1) : d241726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245792, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245792, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65067 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245793 q = 1) : d241727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245793, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245793, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245794 q = 1) : d241728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245794, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245794, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245795 q = 1) : d241729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245795, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245795, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245796 q = 1) : d241730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245796, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245796, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245803 q = 1) : d241737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245803, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245803, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65068 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245804 q = 1) : d241738 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245804, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245804, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245805 q = 1) : d241739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245805, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245805, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245806 q = 1) : d241740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245806, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245806, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245807 q = 1) : d241741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245807, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245807, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245808 q = 1) : d241742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245808, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245808, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65070 (p : Pattern) (ha : d208034 p = 1) (hb : d245814 p = 1) : d241748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245809 q = 1) : d241743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245809, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245809, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65069 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245810 q = 1) : d241744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245810, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245810, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245811 q = 1) : d241745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245811, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245811, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245812 q = 1) : d241746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245812, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245812, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245813 q = 1) : d241747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245813, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245813, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245814 q = 1) : d241748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245814, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245814, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65071 (p : Pattern) (ha : d208034 p = 1) (hb : d245821 p = 1) : d241755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27079 q = 1) (hb : d208034 q = 1) : d241361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64696 q ha hb
    | true =>
      simp only [d27079, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64697 q ha hb
  have h2 (q : Pattern) (ha : d27080 q = 1) (hb : d208034 q = 1) : d241362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27081 q = 1) (hb : d208034 q = 1) : d241363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27081, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27082 q = 1) (hb : d208034 q = 1) : d241364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27083 q = 1) (hb : d208034 q = 1) : d241365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245821 q = 1) : d241755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245821, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245821, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro65072 (p : Pattern) (ha : d208034 p = 1) (hb : d245832 p = 1) : d241766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245827 q = 1) : d241761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245827, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64734 q hb ha
    | true =>
      simp only [d245827, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64705 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245828 q = 1) : d241762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245828, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245828, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245829 q = 1) : d241763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245829, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245829, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245830 q = 1) : d241764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245830, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245830, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245831 q = 1) : d241765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245831, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245831, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245832 q = 1) : d241766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245832, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245832, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65073 (p : Pattern) (ha : d208034 p = 1) (hb : d245838 p = 1) : d241772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27085 q = 1) (hb : d208034 q = 1) : d241367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64695 q ha hb
    | true =>
      simp only [d27085, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64698 q ha hb
  have h2 (q : Pattern) (ha : d27086 q = 1) (hb : d208034 q = 1) : d241368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27086, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245819 q = 1) : d241753 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245819, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245819, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245820 q = 1) : d241754 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245820, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245820, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245822 q = 1) : d241756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245822, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245822, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65071 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245823 q = 1) : d241757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245823, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245823, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245824 q = 1) : d241758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245824, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245824, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245825 q = 1) : d241759 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245825, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245825, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245826 q = 1) : d241760 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245826, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245826, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245833 q = 1) : d241767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245833, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245833, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65072 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245834 q = 1) : d241768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245834, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245834, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245835 q = 1) : d241769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245835, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245835, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245836 q = 1) : d241770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245836, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245836, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245837 q = 1) : d241771 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245837, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245837, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245838 q = 1) : d241772 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245838, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245838, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65074 (p : Pattern) (ha : d208034 p = 1) (hb : d245844 p = 1) : d241778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245839 q = 1) : d241773 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245839, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245839, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65073 q ha hb
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245840 q = 1) : d241774 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245840, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245840, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245841 q = 1) : d241775 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245841, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245841, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245842 q = 1) : d241776 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245842, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245842, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245843 q = 1) : d241777 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245843, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245843, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245844 q = 1) : d241778 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245844, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245844, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65075 (p : Pattern) (ha : d208034 p = 1) (hb : d245850 p = 1) : d241784 p = 1 := by
  have h0 (q : Pattern) (ha : d208034 q = 1) (hb : d245731 q = 1) : d241665 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245731, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65054 q ha hb
    | true =>
      simp only [d245731, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65058 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245758 q = 1) : d241692 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245758, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245758, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65062 q ha hb
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245759 q = 1) : d241693 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245759, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245759, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245786 q = 1) : d241720 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245786, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245786, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65066 q ha hb
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245787 q = 1) : d241721 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245787, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245787, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245788 q = 1) : d241722 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245788, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245788, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208034 q = 1) (hb : d245815 q = 1) : d241749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245815, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245815, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65070 q ha hb
  have h8 (q : Pattern) (ha : d208034 q = 1) (hb : d245816 q = 1) : d241750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245816, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245816, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208034 q = 1) (hb : d245817 q = 1) : d241751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245817, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245817, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208034 q = 1) (hb : d245818 q = 1) : d241752 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245818, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245818, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208034 q = 1) (hb : d245845 q = 1) : d241779 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245845, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245845, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65074 q ha hb
  have h12 (q : Pattern) (ha : d208034 q = 1) (hb : d245846 q = 1) : d241780 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245846, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245846, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208034 q = 1) (hb : d245847 q = 1) : d241781 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245847, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245847, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d208034 q = 1) (hb : d245848 q = 1) : d241782 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245848, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245848, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d208034 q = 1) (hb : d245849 q = 1) : d241783 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245849, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245849, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d208034 q = 1) (hb : d245850 q = 1) : d241784 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245850, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245850, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro65076 (p : Pattern) (ha : d208034 p = 1) (hb : d245856 p = 1) : d241790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245851 q = 1) : d241785 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245851, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65075 q ha hb
    | true =>
      simp only [d245851, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245852 q = 1) : d241786 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245852, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245852, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245853 q = 1) : d241787 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245853, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245853, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245854 q = 1) : d241788 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245854, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245854, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245855 q = 1) : d241789 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245855, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245855, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245856 q = 1) : d241790 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245856, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245856, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65077 (p : Pattern) (ha : d208034 p = 1) (hb : d245862 p = 1) : d241796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245857 q = 1) : d241791 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245857, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65076 q ha hb
    | true =>
      simp only [d245857, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245858 q = 1) : d241792 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245858, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245858, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245859 q = 1) : d241793 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245859, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245859, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245860 q = 1) : d241794 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245860, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245860, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245861 q = 1) : d241795 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245861, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245861, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245862 q = 1) : d241796 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245862, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245862, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65078 (p : Pattern) (ha : d208034 p = 1) (hb : d245868 p = 1) : d241802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245863 q = 1) : d241797 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245863, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65077 q ha hb
    | true =>
      simp only [d245863, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245864 q = 1) : d241798 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245864, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245864, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245865 q = 1) : d241799 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245865, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245865, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245866 q = 1) : d241800 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245866, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245866, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245867 q = 1) : d241801 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245867, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245867, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245868 q = 1) : d241802 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245868, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245868, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65079 (p : Pattern) (ha : d208034 p = 1) (hb : d245874 p = 1) : d241808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245869 q = 1) : d241803 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245869, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65078 q ha hb
    | true =>
      simp only [d245869, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245870 q = 1) : d241804 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245870, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245870, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245871 q = 1) : d241805 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245871, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245871, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245872 q = 1) : d241806 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245872, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245872, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245873 q = 1) : d241807 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245873, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245873, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245874 q = 1) : d241808 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245874, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245874, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65080 (p : Pattern) (ha : d208034 p = 1) (hb : d245880 p = 1) : d241814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245875 q = 1) : d241809 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245875, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65079 q ha hb
    | true =>
      simp only [d245875, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245876 q = 1) : d241810 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245876, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245876, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245877 q = 1) : d241811 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245877, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245877, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245878 q = 1) : d241812 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245878, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245878, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245879 q = 1) : d241813 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245879, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245879, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245880 q = 1) : d241814 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245880, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245880, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65081 (p : Pattern) (ha : d208034 p = 1) (hb : d245886 p = 1) : d241820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245881 q = 1) : d241815 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245881, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65080 q ha hb
    | true =>
      simp only [d245881, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245882 q = 1) : d241816 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245882, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245882, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245883 q = 1) : d241817 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245883, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245883, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245884 q = 1) : d241818 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245884, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245884, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245885 q = 1) : d241819 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245885, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245885, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245886 q = 1) : d241820 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245886, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245886, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65082 (p : Pattern) (ha : d208034 p = 1) (hb : d245892 p = 1) : d241826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208034 q = 1) (hb : d245887 q = 1) : d241821 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245887, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65081 q ha hb
    | true =>
      simp only [d245887, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d208034 q = 1) (hb : d245888 q = 1) : d241822 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245888, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245888, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d208034 q = 1) (hb : d245889 q = 1) : d241823 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245889, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245889, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d208034 q = 1) (hb : d245890 q = 1) : d241824 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245890, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245890, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d208034 q = 1) (hb : d245891 q = 1) : d241825 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245891, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245891, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d208034 q = 1) (hb : d245892 q = 1) : d241826 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245892, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245892, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65083 (p : Pattern) (ha : d208161 p = 1) (hb : d240282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208048 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208048, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64753 q ha hb
    | true =>
      simp only [d208048, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d208151 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208151, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208151, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208158 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208158, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208158, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208159 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208159, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208159, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208160 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208160, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208160, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208161 q = 1) (hb : d240282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208161, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208161, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65084 (p : Pattern) (ha : d208180 p = 1) (hb : d240289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208128 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208048 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208048, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64753 q ha hb
    | true =>
      simp only [d208048, d240224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d208151 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208151, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208151, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208158 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208158, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208158, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208159 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208159, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208159, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208160 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208160, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208160, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208166 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208170 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208055 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208055, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64755 q ha hb
    | true =>
      simp only [d208055, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d208173 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208173, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208173, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208177 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208177, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208177, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208178 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208178, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208178, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208179 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208179, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208179, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208180 q = 1) (hb : d240289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208180, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208180, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65085 (p : Pattern) (ha : d208189 p = 1) (hb : d241616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208055 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208055, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64755 q ha hb
    | true =>
      simp only [d208055, d240231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d208173 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208173, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208173, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208177 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208177, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208177, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208187 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208187, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208187, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208188 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208188, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208188, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208189 q = 1) (hb : d241616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208189, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208189, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65086 (p : Pattern) (ha : d208224 p = 1) (hb : d241626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208085 q = 1) (hb : d240261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208085, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64760 q ha hb
    | true =>
      simp only [d208085, d240261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d208214 q = 1) (hb : d241622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208214, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208214, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208220 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208221 q = 1) (hb : d241623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208221, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208221, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208222 q = 1) (hb : d241624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208222, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208222, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208223 q = 1) (hb : d241625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208223, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208223, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208224 q = 1) (hb : d241626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208224, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208224, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65087 (p : Pattern) (ha : d208230 p = 1) (hb : d241632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208116 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208181 q = 1) (hb : d240290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208181, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65083 q ha hb
    | true =>
      simp only [d208181, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65084 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208184 q = 1) (hb : d240291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208184, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208184, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208185 q = 1) (hb : d241614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208185, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208185, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208186 q = 1) (hb : d241615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208186, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208186, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208190 q = 1) (hb : d241617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208190, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208190, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65085 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208191 q = 1) (hb : d241618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208191, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208191, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208192 q = 1) (hb : d241619 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208192, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208192, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208193 q = 1) (hb : d241620 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208193, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208193, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208194 q = 1) (hb : d241621 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208194, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208194, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208225 q = 1) (hb : d241627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208225, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208225, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65086 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208226 q = 1) (hb : d241628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208226, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208226, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208227 q = 1) (hb : d241629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208227, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208227, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208228 q = 1) (hb : d241630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208228, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208228, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208229 q = 1) (hb : d241631 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208229, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208229, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208230 q = 1) (hb : d241632 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208230, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208230, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65088 (p : Pattern) (ha : d208236 p = 1) (hb : d241638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d208097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d208097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51140 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d208098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d208098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d208099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d208099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d208100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d208100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d208101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d208101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208231 q = 1) (hb : d241633 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208231, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208231, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65087 q ha hb
  have h8 (q : Pattern) (ha : d208232 q = 1) (hb : d241634 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208232, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208232, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208233 q = 1) (hb : d241635 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208233, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208233, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208234 q = 1) (hb : d241636 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208234, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208234, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d208235 q = 1) (hb : d241637 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208235, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208235, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d208236 q = 1) (hb : d241638 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208236, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d208236, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro65089 (p : Pattern) (ha : d208322 p = 1) (hb : d240422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208254 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208254, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64789 q ha hb
    | true =>
      simp only [d208254, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64790 q ha hb
  have h5 (q : Pattern) (ha : d208312 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208312, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208312, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208319 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208319, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208319, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208320 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208320, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208320, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208321 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208321, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208321, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208322 q = 1) (hb : d240422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208322, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208322, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65090 (p : Pattern) (ha : d208343 p = 1) (hb : d240432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208280 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208289 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208254 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208254, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64789 q ha hb
    | true =>
      simp only [d208254, d240417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64790 q ha hb
  have h4 (q : Pattern) (ha : d208312 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208312, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208312, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208318 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208319 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208319, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208319, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208320 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208320, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208320, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208321 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208321, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208321, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208328 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208333 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208264 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208264, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64792 q ha hb
    | true =>
      simp only [d208264, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64793 q ha hb
  have h13 (q : Pattern) (ha : d208336 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208336, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208336, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208340 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208340, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208340, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208341 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208341, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208341, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208342 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208342, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208342, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208343 q = 1) (hb : d240432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208343, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208343, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65091 (p : Pattern) (ha : d208363 p = 1) (hb : d241641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208264 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208264, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64792 q ha hb
    | true =>
      simp only [d208264, d240427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64793 q ha hb
  have h3 (q : Pattern) (ha : d208336 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208336, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208336, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208339 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208340 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208340, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208340, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208361 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208361, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208361, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208362 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208362, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208362, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208363 q = 1) (hb : d241641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208363, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208363, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65092 (p : Pattern) (ha : d208418 p = 1) (hb : d241652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208407 q = 1) (hb : d241647 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208407, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64821 q ha hb
    | true =>
      simp only [d208407, d241647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64824 q ha hb
  have h3 (q : Pattern) (ha : d208408 q = 1) (hb : d241648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208408, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208408, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208414 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208415 q = 1) (hb : d241649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208415, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208415, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208416 q = 1) (hb : d241650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208416, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208416, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208417 q = 1) (hb : d241651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208417, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208417, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208418 q = 1) (hb : d241652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208418, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208418, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65093 (p : Pattern) (ha : d208431 p = 1) (hb : d241658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208272 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208344 q = 1) (hb : d240433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208344, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65089 q ha hb
    | true =>
      simp only [d208344, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65090 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208358 q = 1) (hb : d240434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208358, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208358, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208359 q = 1) (hb : d241639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208359, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208359, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208360 q = 1) (hb : d241640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208360, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208360, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208364 q = 1) (hb : d241642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208364, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208364, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65091 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208366 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208367 q = 1) (hb : d241643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208367, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208367, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208368 q = 1) (hb : d241644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208368, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208368, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208369 q = 1) (hb : d241645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208369, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208369, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208370 q = 1) (hb : d241646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208370, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208370, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208419 q = 1) (hb : d241653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208419, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208419, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65092 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208426 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208427 q = 1) (hb : d241654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208427, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208427, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208428 q = 1) (hb : d241655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208428, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208428, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208429 q = 1) (hb : d241656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208429, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208429, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208430 q = 1) (hb : d241657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208430, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208430, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208431 q = 1) (hb : d241658 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208431, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208431, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65094 (p : Pattern) (ha : d208437 p = 1) (hb : d241664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208432 q = 1) (hb : d241659 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208432, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208432, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65093 q ha hb
  have h2 (q : Pattern) (ha : d208433 q = 1) (hb : d241660 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208433, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208433, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208434 q = 1) (hb : d241661 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208434, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208434, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208435 q = 1) (hb : d241662 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208435, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208435, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208436 q = 1) (hb : d241663 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208436, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208436, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208437 q = 1) (hb : d241664 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208437, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208437, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65095 (p : Pattern) (ha : d208534 p = 1) (hb : d240620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208466 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208466, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64832 q ha hb
    | true =>
      simp only [d208466, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64833 q ha hb
  have h5 (q : Pattern) (ha : d208524 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208524, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208524, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208531 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208531, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208531, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208532 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208532, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208532, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208533 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208533, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208533, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208534 q = 1) (hb : d240620 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208534, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208534, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65096 (p : Pattern) (ha : d208555 p = 1) (hb : d240630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208466 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208466, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64832 q ha hb
    | true =>
      simp only [d208466, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64833 q ha hb
  have h4 (q : Pattern) (ha : d208524 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208524, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208524, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208530 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208531 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208531, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208531, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208532 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208532, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208532, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208533 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208533, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208533, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208545 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208476 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208476, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64835 q ha hb
    | true =>
      simp only [d208476, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64836 q ha hb
  have h13 (q : Pattern) (ha : d208548 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208548, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208548, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208552 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208552, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208552, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208553 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208553, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208553, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208554 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208554, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208554, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208555 q = 1) (hb : d240630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208555, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208555, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65097 (p : Pattern) (ha : d208575 p = 1) (hb : d241668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208476 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208476, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64835 q ha hb
    | true =>
      simp only [d208476, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64836 q ha hb
  have h3 (q : Pattern) (ha : d208548 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208548, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208548, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208551 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208552 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208552, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208552, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208573 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208573, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208573, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208574 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208574, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208574, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208575 q = 1) (hb : d241668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208575, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208575, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65098 (p : Pattern) (ha : d208640 p = 1) (hb : d241679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208629 q = 1) (hb : d241674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208629, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64866 q ha hb
    | true =>
      simp only [d208629, d241674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64869 q ha hb
  have h3 (q : Pattern) (ha : d208630 q = 1) (hb : d241675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208630, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208630, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208636 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208637 q = 1) (hb : d241676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208637, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208637, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208638 q = 1) (hb : d241677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208638, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208638, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208639 q = 1) (hb : d241678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208639, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208639, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208640 q = 1) (hb : d241679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208640, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208640, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65099 (p : Pattern) (ha : d208653 p = 1) (hb : d241685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208556 q = 1) (hb : d240631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208556, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65095 q ha hb
    | true =>
      simp only [d208556, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65096 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208569 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208570 q = 1) (hb : d240632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208570, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208570, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208571 q = 1) (hb : d241666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208571, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208571, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208572 q = 1) (hb : d241667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208572, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208572, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208576 q = 1) (hb : d241669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208576, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208576, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65097 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208578 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208579 q = 1) (hb : d241670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208579, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208579, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208580 q = 1) (hb : d241671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208580, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208580, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208581 q = 1) (hb : d241672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208581, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208581, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208582 q = 1) (hb : d241673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208582, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208582, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208641 q = 1) (hb : d241680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208641, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208641, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65098 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208648 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208649 q = 1) (hb : d241681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208649, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208649, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208650 q = 1) (hb : d241682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208650, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208650, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208651 q = 1) (hb : d241683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208651, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208651, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208652 q = 1) (hb : d241684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208652, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208652, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208653 q = 1) (hb : d241685 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208653, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208653, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65100 (p : Pattern) (ha : d208659 p = 1) (hb : d241691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208654 q = 1) (hb : d241686 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208654, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208654, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65099 q ha hb
  have h2 (q : Pattern) (ha : d208655 q = 1) (hb : d241687 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208655, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208655, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208656 q = 1) (hb : d241688 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208656, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208656, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208657 q = 1) (hb : d241689 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208657, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208657, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208658 q = 1) (hb : d241690 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208658, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208658, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208659 q = 1) (hb : d241691 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208659, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208659, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65101 (p : Pattern) (ha : d208790 p = 1) (hb : d240847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208713 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208713, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64881 q ha hb
    | true =>
      simp only [d208713, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64882 q ha hb
  have h5 (q : Pattern) (ha : d208771 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208771, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d208771, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d208787 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208787, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d208787, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d208788 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208788, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208788, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d208789 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208789, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208789, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d208790 q = 1) (hb : d240847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208790, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208790, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65102 (p : Pattern) (ha : d208811 p = 1) (hb : d240857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208713 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208713, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64881 q ha hb
    | true =>
      simp only [d208713, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64882 q ha hb
  have h4 (q : Pattern) (ha : d208771 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208771, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d208771, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d208786 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d208787 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208787, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d208787, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d208788 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208788, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208788, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208789 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208789, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208789, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d208796 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d208801 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d208723 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208723, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64884 q ha hb
    | true =>
      simp only [d208723, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64885 q ha hb
  have h13 (q : Pattern) (ha : d208804 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208804, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d208804, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208808 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208808, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208808, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208809 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208809, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d208809, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d208810 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208810, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d208810, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d208811 q = 1) (hb : d240857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208811, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d208811, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65103 (p : Pattern) (ha : d208831 p = 1) (hb : d241696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208803 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208723 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208723, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64884 q ha hb
    | true =>
      simp only [d208723, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64885 q ha hb
  have h3 (q : Pattern) (ha : d208804 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208804, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208804, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208808 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208808, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208808, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208829 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208829, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208829, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208830 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208830, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208830, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208831 q = 1) (hb : d241696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208831, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208831, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65104 (p : Pattern) (ha : d208920 p = 1) (hb : d241707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208895 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208900 q = 1) (hb : d241702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208900, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64920 q ha hb
    | true =>
      simp only [d208900, d241702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64926 q ha hb
  have h3 (q : Pattern) (ha : d208901 q = 1) (hb : d241703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d208901, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208901, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208917 q = 1) (hb : d241704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d208917, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208917, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208918 q = 1) (hb : d241705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d208918, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208918, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208919 q = 1) (hb : d241706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d208919, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208919, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d208920 q = 1) (hb : d241707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d208920, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208920, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65105 (p : Pattern) (ha : d208933 p = 1) (hb : d241713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208812 q = 1) (hb : d240858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208812, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65101 q ha hb
    | true =>
      simp only [d208812, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65102 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208825 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208826 q = 1) (hb : d240859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208826, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d208826, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d208827 q = 1) (hb : d241694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208827, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208827, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d208828 q = 1) (hb : d241695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208828, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208828, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d208832 q = 1) (hb : d241697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208832, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208832, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65103 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d208834 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d208835 q = 1) (hb : d241698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208835, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d208835, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d208836 q = 1) (hb : d241699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208836, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d208836, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d208837 q = 1) (hb : d241700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208837, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d208837, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d208838 q = 1) (hb : d241701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208838, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d208838, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d208921 q = 1) (hb : d241708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d208921, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d208921, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65104 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d208928 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d208929 q = 1) (hb : d241709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d208929, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d208929, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d208930 q = 1) (hb : d241710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d208930, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d208930, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d208931 q = 1) (hb : d241711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d208931, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d208931, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d208932 q = 1) (hb : d241712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d208932, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d208932, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d208933 q = 1) (hb : d241713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d208933, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d208933, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65106 (p : Pattern) (ha : d208939 p = 1) (hb : d241719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d208934 q = 1) (hb : d241714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d208934, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208934, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65105 q ha hb
  have h2 (q : Pattern) (ha : d208935 q = 1) (hb : d241715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d208935, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208935, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d208936 q = 1) (hb : d241716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d208936, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208936, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208937 q = 1) (hb : d241717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d208937, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208937, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d208938 q = 1) (hb : d241718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d208938, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208938, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208939 q = 1) (hb : d241719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d208939, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d208939, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65107 (p : Pattern) (ha : d209073 p = 1) (hb : d241099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d208996 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64938 q ha hb
    | true =>
      simp only [d208996, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64939 q ha hb
  have h5 (q : Pattern) (ha : d209054 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209054, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209070 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209070, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d209071 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209071, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209072 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209072, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209073 q = 1) (hb : d241099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209073, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209073, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65108 (p : Pattern) (ha : d209094 p = 1) (hb : d241109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d208996 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d208996, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64938 q ha hb
    | true =>
      simp only [d208996, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64939 q ha hb
  have h4 (q : Pattern) (ha : d209054 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209054, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209054, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209069 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209070 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209070, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209070, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209071 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209071, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209071, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209072 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209072, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209072, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209079 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209084 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d209006 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64941 q ha hb
    | true =>
      simp only [d209006, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64942 q ha hb
  have h13 (q : Pattern) (ha : d209087 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d209087, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209091 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209091, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209092 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209092, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209092, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209093 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209093, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209093, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209094 q = 1) (hb : d241109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209094, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209094, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65109 (p : Pattern) (ha : d209114 p = 1) (hb : d241725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209006 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209006, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64941 q ha hb
    | true =>
      simp only [d209006, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64942 q ha hb
  have h3 (q : Pattern) (ha : d209087 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209087, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209087, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209090 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209091 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209091, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209091, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209112 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209112, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209112, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209113 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209113, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209113, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209114 q = 1) (hb : d241725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209114, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209114, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65110 (p : Pattern) (ha : d209203 p = 1) (hb : d241736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209178 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209183 q = 1) (hb : d241731 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209183, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64977 q ha hb
    | true =>
      simp only [d209183, d241731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64983 q ha hb
  have h3 (q : Pattern) (ha : d209184 q = 1) (hb : d241732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209184, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209184, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209199 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209200 q = 1) (hb : d241733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209200, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209200, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209201 q = 1) (hb : d241734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209201, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209201, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209202 q = 1) (hb : d241735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209202, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209202, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209203 q = 1) (hb : d241736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209203, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209203, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65111 (p : Pattern) (ha : d209216 p = 1) (hb : d241742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209095 q = 1) (hb : d241110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209095, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65107 q ha hb
    | true =>
      simp only [d209095, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209109 q = 1) (hb : d241111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209109, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209109, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209110 q = 1) (hb : d241723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209110, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209110, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209111 q = 1) (hb : d241724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209111, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209111, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209115 q = 1) (hb : d241726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209115, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209115, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65109 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209117 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209118 q = 1) (hb : d241727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209118, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209118, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209119 q = 1) (hb : d241728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209119, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209119, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209120 q = 1) (hb : d241729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209120, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209120, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209121 q = 1) (hb : d241730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209121, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209121, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209204 q = 1) (hb : d241737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209204, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209204, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65110 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209212 q = 1) (hb : d241738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209212, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209212, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209213 q = 1) (hb : d241739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209213, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209213, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209214 q = 1) (hb : d241740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209214, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209214, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209215 q = 1) (hb : d241741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209215, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209215, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209216 q = 1) (hb : d241742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209216, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209216, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65112 (p : Pattern) (ha : d209222 p = 1) (hb : d241748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209217 q = 1) (hb : d241743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209217, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209217, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65111 q ha hb
  have h2 (q : Pattern) (ha : d209218 q = 1) (hb : d241744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209218, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209218, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209219 q = 1) (hb : d241745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209219, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209219, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209220 q = 1) (hb : d241746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209220, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209220, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209221 q = 1) (hb : d241747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209221, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209221, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209222 q = 1) (hb : d241748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209222, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209222, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65113 (p : Pattern) (ha : d209348 p = 1) (hb : d241356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d209278 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64995 q ha hb
    | true =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64996 q ha hb
  have h5 (q : Pattern) (ha : d209329 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d209329, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d209345 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209345, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d209346 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209346, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209347 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209347, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209348 q = 1) (hb : d241356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209348, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209348, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65114 (p : Pattern) (ha : d209369 p = 1) (hb : d241366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209278 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64995 q ha hb
    | true =>
      simp only [d209278, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64996 q ha hb
  have h4 (q : Pattern) (ha : d209329 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209329, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d209329, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d209344 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d209345 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209345, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209345, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d209346 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209346, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209346, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209347 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209347, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209347, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d209354 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d209359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d209288 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64998 q ha hb
    | true =>
      simp only [d209288, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64999 q ha hb
  have h13 (q : Pattern) (ha : d209362 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d209362, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209366 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209366, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209367 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209367, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d209367, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d209368 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209368, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d209368, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d209369 q = 1) (hb : d241366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209369, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d209369, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65115 (p : Pattern) (ha : d209389 p = 1) (hb : d241755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209288 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209288, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64998 q ha hb
    | true =>
      simp only [d209288, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64999 q ha hb
  have h3 (q : Pattern) (ha : d209362 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209362, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209362, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209365 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209366 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209366, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209366, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209387 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209387, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209387, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209388 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209388, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209388, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209389 q = 1) (hb : d241755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209389, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209389, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65116 (p : Pattern) (ha : d209474 p = 1) (hb : d241766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d209449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d209454 q = 1) (hb : d241761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d209454, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65033 q ha hb
    | true =>
      simp only [d209454, d241761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65039 q ha hb
  have h3 (q : Pattern) (ha : d209455 q = 1) (hb : d241762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d209455, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209455, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d209470 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209471 q = 1) (hb : d241763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d209471, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209471, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209472 q = 1) (hb : d241764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d209472, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209472, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209473 q = 1) (hb : d241765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d209473, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209473, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d209474 q = 1) (hb : d241766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d209474, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209474, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65117 (p : Pattern) (ha : d209487 p = 1) (hb : d241772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209296 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209370 q = 1) (hb : d241367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209370, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65113 q ha hb
    | true =>
      simp only [d209370, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65114 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d209383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d209384 q = 1) (hb : d241368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209384, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209384, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d209385 q = 1) (hb : d241753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209385, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209385, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d209386 q = 1) (hb : d241754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209386, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209386, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209390 q = 1) (hb : d241756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209390, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209390, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65115 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d209392 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d209393 q = 1) (hb : d241757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209393, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d209393, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d209394 q = 1) (hb : d241758 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209394, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d209394, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d209395 q = 1) (hb : d241759 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209395, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209395, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d209396 q = 1) (hb : d241760 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209396, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209396, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209475 q = 1) (hb : d241767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d209475, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d209475, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65116 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d209482 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d209483 q = 1) (hb : d241768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d209483, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d209483, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d209484 q = 1) (hb : d241769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d209484, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209484, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d209485 q = 1) (hb : d241770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d209485, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d209485, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d209486 q = 1) (hb : d241771 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d209486, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d209486, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d209487 q = 1) (hb : d241772 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d209487, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d209487, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65118 (p : Pattern) (ha : d209493 p = 1) (hb : d241778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209488 q = 1) (hb : d241773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d209488, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209488, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65117 q ha hb
  have h2 (q : Pattern) (ha : d209489 q = 1) (hb : d241774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d209489, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209489, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d209490 q = 1) (hb : d241775 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d209490, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209490, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d209491 q = 1) (hb : d241776 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d209491, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209491, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d209492 q = 1) (hb : d241777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d209492, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209492, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d209493 q = 1) (hb : d241778 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d209493, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d209493, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65119 (p : Pattern) (ha : d209499 p = 1) (hb : d241784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d208438 q = 1) (hb : d241665 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208438, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65088 q ha hb
    | true =>
      simp only [d208438, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65094 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d208660 q = 1) (hb : d241692 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208660, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208660, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65100 q ha hb
  have h3 (q : Pattern) (ha : d208661 q = 1) (hb : d241693 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208661, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d208661, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d208940 q = 1) (hb : d241720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d208940, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208940, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65106 q ha hb
  have h5 (q : Pattern) (ha : d208941 q = 1) (hb : d241721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d208941, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d208941, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d208942 q = 1) (hb : d241722 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d208942, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d208942, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d209223 q = 1) (hb : d241749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209223, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209223, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65112 q ha hb
  have h8 (q : Pattern) (ha : d209224 q = 1) (hb : d241750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209224, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209224, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d209225 q = 1) (hb : d241751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209225, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209225, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d209226 q = 1) (hb : d241752 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209226, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d209226, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d209494 q = 1) (hb : d241779 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d209494, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209494, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65118 q ha hb
  have h12 (q : Pattern) (ha : d209495 q = 1) (hb : d241780 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d209495, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209495, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d209496 q = 1) (hb : d241781 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d209496, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209496, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d209497 q = 1) (hb : d241782 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d209497, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d209497, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d209498 q = 1) (hb : d241783 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d209498, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d209498, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d209499 q = 1) (hb : d241784 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d209499, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d209499, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro65120 (p : Pattern) (ha : d209505 p = 1) (hb : d241790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209500 q = 1) (hb : d241785 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d209500, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65119 q ha hb
    | true =>
      simp only [d209500, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209501 q = 1) (hb : d241786 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d209501, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209501, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209502 q = 1) (hb : d241787 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d209502, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209502, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209503 q = 1) (hb : d241788 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d209503, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209503, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209504 q = 1) (hb : d241789 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d209504, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209504, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209505 q = 1) (hb : d241790 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d209505, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209505, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65121 (p : Pattern) (ha : d209511 p = 1) (hb : d241796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209506 q = 1) (hb : d241791 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d209506, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65120 q ha hb
    | true =>
      simp only [d209506, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209507 q = 1) (hb : d241792 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d209507, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209507, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209508 q = 1) (hb : d241793 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d209508, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209508, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209509 q = 1) (hb : d241794 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d209509, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209509, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209510 q = 1) (hb : d241795 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d209510, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209510, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209511 q = 1) (hb : d241796 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d209511, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209511, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65122 (p : Pattern) (ha : d209517 p = 1) (hb : d241802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209512 q = 1) (hb : d241797 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d209512, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65121 q ha hb
    | true =>
      simp only [d209512, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209513 q = 1) (hb : d241798 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d209513, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209513, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209514 q = 1) (hb : d241799 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d209514, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209514, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209515 q = 1) (hb : d241800 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d209515, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209515, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209516 q = 1) (hb : d241801 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d209516, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209516, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209517 q = 1) (hb : d241802 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d209517, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209517, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65123 (p : Pattern) (ha : d209523 p = 1) (hb : d241808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209518 q = 1) (hb : d241803 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d209518, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65122 q ha hb
    | true =>
      simp only [d209518, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209519 q = 1) (hb : d241804 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d209519, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209519, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209520 q = 1) (hb : d241805 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d209520, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209520, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209521 q = 1) (hb : d241806 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d209521, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209521, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209522 q = 1) (hb : d241807 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d209522, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209522, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209523 q = 1) (hb : d241808 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d209523, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209523, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65124 (p : Pattern) (ha : d209529 p = 1) (hb : d241814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209524 q = 1) (hb : d241809 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d209524, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65123 q ha hb
    | true =>
      simp only [d209524, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209525 q = 1) (hb : d241810 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d209525, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209525, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209526 q = 1) (hb : d241811 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d209526, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209526, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209527 q = 1) (hb : d241812 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d209527, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209527, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209528 q = 1) (hb : d241813 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d209528, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209528, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209529 q = 1) (hb : d241814 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d209529, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209529, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65125 (p : Pattern) (ha : d209535 p = 1) (hb : d241820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209530 q = 1) (hb : d241815 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d209530, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65124 q ha hb
    | true =>
      simp only [d209530, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209531 q = 1) (hb : d241816 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d209531, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209531, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209532 q = 1) (hb : d241817 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d209532, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209532, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209533 q = 1) (hb : d241818 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d209533, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209533, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209534 q = 1) (hb : d241819 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d209534, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209534, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209535 q = 1) (hb : d241820 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d209535, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209535, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65126 (p : Pattern) (ha : d209541 p = 1) (hb : d241826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d209536 q = 1) (hb : d241821 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d209536, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65125 q ha hb
    | true =>
      simp only [d209536, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d209537 q = 1) (hb : d241822 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d209537, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d209537, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d209538 q = 1) (hb : d241823 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d209538, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d209538, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d209539 q = 1) (hb : d241824 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d209539, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d209539, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d209540 q = 1) (hb : d241825 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d209540, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d209540, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d209541 q = 1) (hb : d241826 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d209541, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d209541, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro65127 (p : Pattern) (ha : d211124 p = 1) (hb : d240282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211120 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211120, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211121 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211121, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211122 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211122, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211123 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211123, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211124 q = 1) (hb : d240282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211124, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211124, d240282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65128 (p : Pattern) (ha : d211129 p = 1) (hb : d240289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23249 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240224 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211120 q = 1) (hb : d240278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211120, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211120, d240278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23270 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211121 q = 1) (hb : d240279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211121, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211121, d240279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211122 q = 1) (hb : d240280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211122, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211122, d240280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211123 q = 1) (hb : d240281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211123, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211123, d240281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23279 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23283 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211125 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211125, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211126 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211126, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211127 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211127, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211127, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211128 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211128, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211128, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211129 q = 1) (hb : d240289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211129, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211129, d240289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65129 (p : Pattern) (ha : d211136 p = 1) (hb : d241616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211125 q = 1) (hb : d240285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211125, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211125, d240285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211126 q = 1) (hb : d240286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211126, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211126, d240286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211134 q = 1) (hb : d240287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211134, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211134, d240287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211135 q = 1) (hb : d240288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211135, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211135, d240288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211136 q = 1) (hb : d241616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211136, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211136, d241616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65130 (p : Pattern) (ha : d211146 p = 1) (hb : d241626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240261 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211142 q = 1) (hb : d241622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211142, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211142, d241622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23349 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211143 q = 1) (hb : d241623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211143, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211143, d241623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211144 q = 1) (hb : d241624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211144, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211144, d241624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211145 q = 1) (hb : d241625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211145, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211145, d241625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211146 q = 1) (hb : d241626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211146, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211146, d241626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65131 (p : Pattern) (ha : d211152 p = 1) (hb : d241632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211130 q = 1) (hb : d240290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211130, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65127 q ha hb
    | true =>
      simp only [d211130, d240290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65128 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23298 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211131 q = 1) (hb : d240291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211131, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211131, d240291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211132 q = 1) (hb : d241614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211132, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211132, d241614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211133 q = 1) (hb : d241615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211133, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211133, d241615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211137 q = 1) (hb : d241617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211137, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211137, d241617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65129 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211138 q = 1) (hb : d241618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211138, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211138, d241618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211139 q = 1) (hb : d241619 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211139, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211139, d241619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211140 q = 1) (hb : d241620 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211140, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211140, d241620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211141 q = 1) (hb : d241621 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211141, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211141, d241621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211147 q = 1) (hb : d241627 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211147, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211147, d241627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65130 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211148 q = 1) (hb : d241628 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211148, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211148, d241628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211149 q = 1) (hb : d241629 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211149, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211149, d241629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211150 q = 1) (hb : d241630 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211150, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211150, d241630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211151 q = 1) (hb : d241631 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211151, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211151, d241631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211152 q = 1) (hb : d241632 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211152, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211152, d241632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65132 (p : Pattern) (ha : d211158 p = 1) (hb : d241638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d211115 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d211115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51189 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d211116 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d211116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d211117 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d211117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d211118 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d211118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d211119 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d211119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211153 q = 1) (hb : d241633 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211153, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211153, d241633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65131 q ha hb
  have h8 (q : Pattern) (ha : d211154 q = 1) (hb : d241634 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211154, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211154, d241634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211155 q = 1) (hb : d241635 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211155, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211155, d241635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211156 q = 1) (hb : d241636 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211156, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211156, d241636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211157 q = 1) (hb : d241637 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211157, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211157, d241637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d211158 q = 1) (hb : d241638 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211158, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d211158, d241638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro65133 (p : Pattern) (ha : d211163 p = 1) (hb : d240422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211159 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211159, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211160 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211160, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211161 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211161, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211162 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211162, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211163 q = 1) (hb : d240422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211163, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211163, d240422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65134 (p : Pattern) (ha : d211168 p = 1) (hb : d240432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23409 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23440 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211159 q = 1) (hb : d240418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211159, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211159, d240418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211160 q = 1) (hb : d240419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211160, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211160, d240419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211161 q = 1) (hb : d240420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211161, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211161, d240420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211162 q = 1) (hb : d240421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211162, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211162, d240421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211164 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211164, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211165 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211165, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211166 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211166, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211166, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211167 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211167, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211167, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211168 q = 1) (hb : d240432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211168, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211168, d240432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65135 (p : Pattern) (ha : d211175 p = 1) (hb : d241641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211164 q = 1) (hb : d240428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211164, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211164, d240428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211165 q = 1) (hb : d240429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211165, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211165, d240429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211173 q = 1) (hb : d240430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211173, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211173, d240430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211174 q = 1) (hb : d240431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211174, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211174, d240431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211175 q = 1) (hb : d241641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211175, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211175, d241641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65136 (p : Pattern) (ha : d211185 p = 1) (hb : d241652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211181 q = 1) (hb : d241648 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211181, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211181, d241648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23600 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211182 q = 1) (hb : d241649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211182, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211182, d241649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211183 q = 1) (hb : d241650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211183, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211183, d241650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211184 q = 1) (hb : d241651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211184, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211184, d241651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211185 q = 1) (hb : d241652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211185, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211185, d241652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65137 (p : Pattern) (ha : d211191 p = 1) (hb : d241658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211169 q = 1) (hb : d240433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211169, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65133 q ha hb
    | true =>
      simp only [d211169, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65134 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211170 q = 1) (hb : d240434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211170, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211170, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211171 q = 1) (hb : d241639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211171, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211171, d241639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211172 q = 1) (hb : d241640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211172, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211172, d241640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211176 q = 1) (hb : d241642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211176, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211176, d241642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65135 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211177 q = 1) (hb : d241643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211177, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211177, d241643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211178 q = 1) (hb : d241644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211178, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211178, d241644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211179 q = 1) (hb : d241645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211179, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211179, d241645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211180 q = 1) (hb : d241646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211180, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211180, d241646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211186 q = 1) (hb : d241653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211186, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211186, d241653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65136 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23616 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211187 q = 1) (hb : d241654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211187, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211187, d241654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211188 q = 1) (hb : d241655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211188, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211188, d241655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211189 q = 1) (hb : d241656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211189, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211189, d241656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211190 q = 1) (hb : d241657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211190, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211190, d241657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211191 q = 1) (hb : d241658 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211191, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211191, d241658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65138 (p : Pattern) (ha : d211197 p = 1) (hb : d241664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211192 q = 1) (hb : d241659 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211192, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211192, d241659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65137 q ha hb
  have h2 (q : Pattern) (ha : d211193 q = 1) (hb : d241660 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211193, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211193, d241660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211194 q = 1) (hb : d241661 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211194, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211194, d241661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211195 q = 1) (hb : d241662 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211195, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211195, d241662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211196 q = 1) (hb : d241663 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211196, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211196, d241663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211197 q = 1) (hb : d241664 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211197, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211197, d241664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65139 (p : Pattern) (ha : d211203 p = 1) (hb : d240620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211199 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211199, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211200 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211200, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211201 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211201, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211202 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211202, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211203 q = 1) (hb : d240620 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211203, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211203, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65140 (p : Pattern) (ha : d211208 p = 1) (hb : d240630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240615 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211199 q = 1) (hb : d240616 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211199, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211199, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d23758 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211200 q = 1) (hb : d240617 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211200, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211200, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211201 q = 1) (hb : d240618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211201, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211201, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211202 q = 1) (hb : d240619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211202, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211202, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d23768 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d23773 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211204 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211204, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211205 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211205, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211206 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211206, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211206, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211207 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211207, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211207, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211208 q = 1) (hb : d240630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211208, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211208, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65141 (p : Pattern) (ha : d211215 p = 1) (hb : d241668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240625 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211204 q = 1) (hb : d240626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211204, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211204, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211205 q = 1) (hb : d240627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211205, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211205, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211213 q = 1) (hb : d240628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211213, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211213, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211214 q = 1) (hb : d240629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211214, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211214, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211215 q = 1) (hb : d241668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211215, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211215, d241668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65142 (p : Pattern) (ha : d211225 p = 1) (hb : d241679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211221 q = 1) (hb : d241675 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211221, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211221, d241675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23897 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211222 q = 1) (hb : d241676 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211222, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211222, d241676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211223 q = 1) (hb : d241677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211223, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211223, d241677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211224 q = 1) (hb : d241678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211224, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211224, d241678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211225 q = 1) (hb : d241679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211225, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211225, d241679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65143 (p : Pattern) (ha : d211231 p = 1) (hb : d241685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211209 q = 1) (hb : d240631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211209, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65139 q ha hb
    | true =>
      simp only [d211209, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65140 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d23800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211210 q = 1) (hb : d240632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211210, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211210, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211211 q = 1) (hb : d241666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211211, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211211, d241666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211212 q = 1) (hb : d241667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211212, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211212, d241667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211216 q = 1) (hb : d241669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211216, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211216, d241669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65141 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d23809 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211217 q = 1) (hb : d241670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211217, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211217, d241670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211218 q = 1) (hb : d241671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211218, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211218, d241671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211219 q = 1) (hb : d241672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211219, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211219, d241672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211220 q = 1) (hb : d241673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211220, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211220, d241673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211226 q = 1) (hb : d241680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211226, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211226, d241680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65142 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23913 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211227 q = 1) (hb : d241681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211227, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211227, d241681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211228 q = 1) (hb : d241682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211228, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211228, d241682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211229 q = 1) (hb : d241683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211229, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211229, d241683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211230 q = 1) (hb : d241684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211230, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211230, d241684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211231 q = 1) (hb : d241685 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211231, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211231, d241685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65144 (p : Pattern) (ha : d211237 p = 1) (hb : d241691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211232 q = 1) (hb : d241686 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211232, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211232, d241686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65143 q ha hb
  have h2 (q : Pattern) (ha : d211233 q = 1) (hb : d241687 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211233, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211233, d241687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211234 q = 1) (hb : d241688 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211234, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211234, d241688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211235 q = 1) (hb : d241689 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211235, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211235, d241689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211236 q = 1) (hb : d241690 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211236, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211236, d241690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211237 q = 1) (hb : d241691 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211237, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211237, d241691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65145 (p : Pattern) (ha : d211244 p = 1) (hb : d240847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211240 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211240, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211241 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211241, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211242 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211242, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211243 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211243, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211244 q = 1) (hb : d240847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211244, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211244, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65146 (p : Pattern) (ha : d211249 p = 1) (hb : d240857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24004 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d240842 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211240 q = 1) (hb : d240843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211240, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211240, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211241 q = 1) (hb : d240844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211241, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211241, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211242 q = 1) (hb : d240845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211242, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211242, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211243 q = 1) (hb : d240846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211243, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211243, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24115 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24120 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211245 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211245, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211246 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211246, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211247 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211247, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211247, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211248 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211248, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211248, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211249 q = 1) (hb : d240857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211249, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211249, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65147 (p : Pattern) (ha : d211256 p = 1) (hb : d241696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d240852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211245 q = 1) (hb : d240853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211245, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211245, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24129 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211246 q = 1) (hb : d240854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211246, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211246, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211254 q = 1) (hb : d240855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211254, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211254, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211255 q = 1) (hb : d240856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211255, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211255, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211256 q = 1) (hb : d241696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211256, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211256, d241696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65148 (p : Pattern) (ha : d211266 p = 1) (hb : d241707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24217 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241702 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211262 q = 1) (hb : d241703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211262, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211262, d241703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211263 q = 1) (hb : d241704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211263, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211263, d241704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211264 q = 1) (hb : d241705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211264, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211264, d241705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211265 q = 1) (hb : d241706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211265, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211265, d241706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211266 q = 1) (hb : d241707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211266, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211266, d241707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65149 (p : Pattern) (ha : d211272 p = 1) (hb : d241713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d23996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211250 q = 1) (hb : d240858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211250, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65145 q ha hb
    | true =>
      simp only [d211250, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65146 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24147 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211251 q = 1) (hb : d240859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211251, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211251, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211252 q = 1) (hb : d241694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211252, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211252, d241694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211253 q = 1) (hb : d241695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211253, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211253, d241695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211257 q = 1) (hb : d241697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211257, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211257, d241697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65147 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24156 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211258 q = 1) (hb : d241698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211258, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211258, d241698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211259 q = 1) (hb : d241699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211259, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211259, d241699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211260 q = 1) (hb : d241700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211260, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211260, d241700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211261 q = 1) (hb : d241701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211261, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211261, d241701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211267 q = 1) (hb : d241708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211267, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211267, d241708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65148 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24292 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211268 q = 1) (hb : d241709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211268, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211268, d241709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211269 q = 1) (hb : d241710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211269, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211269, d241710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211270 q = 1) (hb : d241711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211270, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211270, d241711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211271 q = 1) (hb : d241712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211271, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211271, d241712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211272 q = 1) (hb : d241713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211272, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211272, d241713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65150 (p : Pattern) (ha : d211278 p = 1) (hb : d241719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211273 q = 1) (hb : d241714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211273, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211273, d241714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65149 q ha hb
  have h2 (q : Pattern) (ha : d211274 q = 1) (hb : d241715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211274, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211274, d241715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211275 q = 1) (hb : d241716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211275, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211275, d241716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211276 q = 1) (hb : d241717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211276, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211276, d241717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211277 q = 1) (hb : d241718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211277, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211277, d241718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211278 q = 1) (hb : d241719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211278, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211278, d241719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65151 (p : Pattern) (ha : d211286 p = 1) (hb : d241099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211282 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211282, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211282, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211283 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211283, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211283, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211284 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211284, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211284, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211285 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211285, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211285, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211286 q = 1) (hb : d241099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211286, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211286, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65152 (p : Pattern) (ha : d211291 p = 1) (hb : d241109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241094 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211282 q = 1) (hb : d241095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211282, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211282, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24487 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211283 q = 1) (hb : d241096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211283, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211283, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211284 q = 1) (hb : d241097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211284, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211284, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211285 q = 1) (hb : d241098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211285, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211285, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24502 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211287 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211287, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211287, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211288 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211288, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211288, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211289 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211289, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211289, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211290 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211290, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211290, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211291 q = 1) (hb : d241109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211291, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211291, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65153 (p : Pattern) (ha : d211298 p = 1) (hb : d241725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211287 q = 1) (hb : d241105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211287, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211287, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211288 q = 1) (hb : d241106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211288, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211288, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211296 q = 1) (hb : d241107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211296, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211296, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211297 q = 1) (hb : d241108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211297, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211297, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211298 q = 1) (hb : d241725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211298, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211298, d241725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65154 (p : Pattern) (ha : d211308 p = 1) (hb : d241736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211304 q = 1) (hb : d241732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211304, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211304, d241732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24658 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211305 q = 1) (hb : d241733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211305, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211305, d241733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211306 q = 1) (hb : d241734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211306, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211306, d241734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211307 q = 1) (hb : d241735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211307, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211307, d241735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211308 q = 1) (hb : d241736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211308, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211308, d241736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65155 (p : Pattern) (ha : d211314 p = 1) (hb : d241742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24378 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211292 q = 1) (hb : d241110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211292, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65151 q ha hb
    | true =>
      simp only [d211292, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65152 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211293 q = 1) (hb : d241111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211293, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211293, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211294 q = 1) (hb : d241723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211294, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211294, d241723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211295 q = 1) (hb : d241724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211295, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211295, d241724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211299 q = 1) (hb : d241726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211299, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211299, d241726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65153 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24538 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211300 q = 1) (hb : d241727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211300, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211300, d241727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211301 q = 1) (hb : d241728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211301, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211301, d241728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211302 q = 1) (hb : d241729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211302, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211302, d241729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211303 q = 1) (hb : d241730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211303, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211303, d241730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211309 q = 1) (hb : d241737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211309, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211309, d241737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65154 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24674 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211310 q = 1) (hb : d241738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211310, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211310, d241738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211311 q = 1) (hb : d241739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211311, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211311, d241739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211312 q = 1) (hb : d241740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211312, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211312, d241740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211313 q = 1) (hb : d241741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211313, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211313, d241741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211314 q = 1) (hb : d241742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211314, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211314, d241742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65156 (p : Pattern) (ha : d211320 p = 1) (hb : d241748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211315 q = 1) (hb : d241743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211315, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211315, d241743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65155 q ha hb
  have h2 (q : Pattern) (ha : d211316 q = 1) (hb : d241744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211316, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211316, d241744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211317 q = 1) (hb : d241745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211317, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211317, d241745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211318 q = 1) (hb : d241746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211318, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211318, d241746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211319 q = 1) (hb : d241747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211319, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211319, d241747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211320 q = 1) (hb : d241748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211320, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211320, d241748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65157 (p : Pattern) (ha : d211329 p = 1) (hb : d241356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211325 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211325, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211325, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211326 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211326, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211326, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211327 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211327, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211327, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211328 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211328, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211328, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211329 q = 1) (hb : d241356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211329, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211329, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro65158 (p : Pattern) (ha : d211334 p = 1) (hb : d241366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211325 q = 1) (hb : d241352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211325, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211325, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d24859 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211326 q = 1) (hb : d241353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211326, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211326, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211327 q = 1) (hb : d241354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211327, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211327, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211328 q = 1) (hb : d241355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211328, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211328, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d24874 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d211330 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211330, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211330, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211331 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211331, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211331, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211332 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211332, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211332, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211333 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211333, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211333, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211334 q = 1) (hb : d241366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211334, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211334, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro65159 (p : Pattern) (ha : d211341 p = 1) (hb : d241755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24876 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241361 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211330 q = 1) (hb : d241362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211330, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211330, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d24883 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211331 q = 1) (hb : d241363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211331, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211331, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211339 q = 1) (hb : d241364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211339, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211339, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211340 q = 1) (hb : d241365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211340, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211340, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211341 q = 1) (hb : d241755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211341, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211341, d241755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65160 (p : Pattern) (ha : d211351 p = 1) (hb : d241766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241761 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211347 q = 1) (hb : d241762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211347, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211347, d241762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211348 q = 1) (hb : d241763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211348, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211348, d241763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211349 q = 1) (hb : d241764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211349, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211349, d241764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211350 q = 1) (hb : d241765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211350, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211350, d241765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211351 q = 1) (hb : d241766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211351, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211351, d241766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65161 (p : Pattern) (ha : d211357 p = 1) (hb : d241772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d24759 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211335 q = 1) (hb : d241367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211335, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65157 q ha hb
    | true =>
      simp only [d211335, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65158 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d24901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211336 q = 1) (hb : d241368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211336, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211336, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211337 q = 1) (hb : d241753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211337, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211337, d241753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211338 q = 1) (hb : d241754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211338, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211338, d241754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211342 q = 1) (hb : d241756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211342, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211342, d241756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65159 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d24910 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211343 q = 1) (hb : d241757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211343, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211343, d241757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211344 q = 1) (hb : d241758 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211344, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211344, d241758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d211345 q = 1) (hb : d241759 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211345, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211345, d241759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d211346 q = 1) (hb : d241760 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211346, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211346, d241760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211352 q = 1) (hb : d241767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211352, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211352, d241767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65160 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25042 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211353 q = 1) (hb : d241768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211353, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211353, d241768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211354 q = 1) (hb : d241769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211354, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211354, d241769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d211355 q = 1) (hb : d241770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211355, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211355, d241770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d211356 q = 1) (hb : d241771 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211356, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211356, d241771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d211357 q = 1) (hb : d241772 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211357, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211357, d241772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65162 (p : Pattern) (ha : d211363 p = 1) (hb : d241778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211358 q = 1) (hb : d241773 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211358, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211358, d241773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65161 q ha hb
  have h2 (q : Pattern) (ha : d211359 q = 1) (hb : d241774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211359, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211359, d241774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211360 q = 1) (hb : d241775 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211360, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211360, d241775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211361 q = 1) (hb : d241776 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211361, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211361, d241776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211362 q = 1) (hb : d241777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211362, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211362, d241777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211363 q = 1) (hb : d241778 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211363, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211363, d241778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65163 (p : Pattern) (ha : d211369 p = 1) (hb : d241784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d211198 q = 1) (hb : d241665 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211198, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65132 q ha hb
    | true =>
      simp only [d211198, d241665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65138 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211238 q = 1) (hb : d241692 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211238, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211238, d241692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65144 q ha hb
  have h3 (q : Pattern) (ha : d211239 q = 1) (hb : d241693 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211239, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d211239, d241693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211279 q = 1) (hb : d241720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211279, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211279, d241720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65150 q ha hb
  have h5 (q : Pattern) (ha : d211280 q = 1) (hb : d241721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211280, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211280, d241721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211281 q = 1) (hb : d241722 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211281, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211281, d241722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211321 q = 1) (hb : d241749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211321, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211321, d241749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65156 q ha hb
  have h8 (q : Pattern) (ha : d211322 q = 1) (hb : d241750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211322, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211322, d241750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211323 q = 1) (hb : d241751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211323, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211323, d241751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211324 q = 1) (hb : d241752 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211324, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211324, d241752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211364 q = 1) (hb : d241779 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211364, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211364, d241779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65162 q ha hb
  have h12 (q : Pattern) (ha : d211365 q = 1) (hb : d241780 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211365, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211365, d241780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211366 q = 1) (hb : d241781 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211366, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211366, d241781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d211367 q = 1) (hb : d241782 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211367, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211367, d241782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d211368 q = 1) (hb : d241783 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d211368, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211368, d241783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d211369 q = 1) (hb : d241784 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d211369, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211369, d241784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro65164 (p : Pattern) (ha : d211375 p = 1) (hb : d241790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211370 q = 1) (hb : d241785 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d211370, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65163 q ha hb
    | true =>
      simp only [d211370, d241785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211371 q = 1) (hb : d241786 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d211371, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211371, d241786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211372 q = 1) (hb : d241787 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d211372, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211372, d241787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211373 q = 1) (hb : d241788 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d211373, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211373, d241788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211374 q = 1) (hb : d241789 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d211374, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211374, d241789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211375 q = 1) (hb : d241790 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d211375, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211375, d241790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65165 (p : Pattern) (ha : d211381 p = 1) (hb : d241796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211376 q = 1) (hb : d241791 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d211376, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65164 q ha hb
    | true =>
      simp only [d211376, d241791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211377 q = 1) (hb : d241792 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d211377, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211377, d241792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211378 q = 1) (hb : d241793 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d211378, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211378, d241793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211379 q = 1) (hb : d241794 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d211379, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211379, d241794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211380 q = 1) (hb : d241795 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d211380, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211380, d241795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211381 q = 1) (hb : d241796 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d211381, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211381, d241796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65166 (p : Pattern) (ha : d211387 p = 1) (hb : d241802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211382 q = 1) (hb : d241797 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d211382, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65165 q ha hb
    | true =>
      simp only [d211382, d241797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211383 q = 1) (hb : d241798 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d211383, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211383, d241798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211384 q = 1) (hb : d241799 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d211384, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211384, d241799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211385 q = 1) (hb : d241800 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d211385, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211385, d241800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211386 q = 1) (hb : d241801 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d211386, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211386, d241801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211387 q = 1) (hb : d241802 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d211387, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211387, d241802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65167 (p : Pattern) (ha : d211393 p = 1) (hb : d241808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211388 q = 1) (hb : d241803 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d211388, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65166 q ha hb
    | true =>
      simp only [d211388, d241803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211389 q = 1) (hb : d241804 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d211389, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211389, d241804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211390 q = 1) (hb : d241805 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d211390, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211390, d241805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211391 q = 1) (hb : d241806 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d211391, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211391, d241806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211392 q = 1) (hb : d241807 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d211392, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211392, d241807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211393 q = 1) (hb : d241808 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d211393, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211393, d241808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65168 (p : Pattern) (ha : d211399 p = 1) (hb : d241814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211394 q = 1) (hb : d241809 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d211394, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65167 q ha hb
    | true =>
      simp only [d211394, d241809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211395 q = 1) (hb : d241810 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d211395, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211395, d241810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211396 q = 1) (hb : d241811 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d211396, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211396, d241811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211397 q = 1) (hb : d241812 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d211397, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211397, d241812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211398 q = 1) (hb : d241813 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d211398, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211398, d241813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211399 q = 1) (hb : d241814 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d211399, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211399, d241814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65169 (p : Pattern) (ha : d211405 p = 1) (hb : d241820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211400 q = 1) (hb : d241815 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d211400, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65168 q ha hb
    | true =>
      simp only [d211400, d241815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211401 q = 1) (hb : d241816 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d211401, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211401, d241816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211402 q = 1) (hb : d241817 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d211402, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211402, d241817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211403 q = 1) (hb : d241818 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d211403, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211403, d241818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211404 q = 1) (hb : d241819 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d211404, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211404, d241819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211405 q = 1) (hb : d241820 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d211405, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211405, d241820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65170 (p : Pattern) (ha : d211411 p = 1) (hb : d241826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211406 q = 1) (hb : d241821 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d211406, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65169 q ha hb
    | true =>
      simp only [d211406, d241821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d211407 q = 1) (hb : d241822 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d211407, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211407, d241822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d211408 q = 1) (hb : d241823 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d211408, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211408, d241823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d211409 q = 1) (hb : d241824 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d211409, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211409, d241824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d211410 q = 1) (hb : d241825 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d211410, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211410, d241825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d211411 q = 1) (hb : d241826 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d211411, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211411, d241826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65171 (p : Pattern) (ha : d25104 p = 1) (hb : d231381 p = 1) : d29114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25102 q = 1) (hb : d231381 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d231381, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25102, d231381, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25103 q = 1) (hb : d231381 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25103, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25104 q = 1) (hb : d231381 q = 1) : d29114 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25104, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro65172 (p : Pattern) (ha : d25110 p = 1) (hb : d231381 p = 1) : d234713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25105 q = 1) (hb : d231381 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65171 q ha hb
    | true =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25106 q = 1) (hb : d231381 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25107 q = 1) (hb : d231381 q = 1) : d29117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25108 q = 1) (hb : d231381 q = 1) : d29118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25108, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25109 q = 1) (hb : d231381 q = 1) : d29119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25109, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25110 q = 1) (hb : d231381 q = 1) : d234713 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d234713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25110, d234713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65173 (p : Pattern) (ha : d25116 p = 1) (hb : d231381 p = 1) : d234719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25111 q = 1) (hb : d231381 q = 1) : d234714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
    | true =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
  have h2 (q : Pattern) (ha : d25112 q = 1) (hb : d231381 q = 1) : d234715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25113 q = 1) (hb : d231381 q = 1) : d234716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25114 q = 1) (hb : d231381 q = 1) : d234717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25114, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25115 q = 1) (hb : d231381 q = 1) : d234718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d234718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25115, d234718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25116 q = 1) (hb : d231381 q = 1) : d234719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d234719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25116, d234719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro65174 (p : Pattern) (ha : d25122 p = 1) (hb : d231381 p = 1) : d234725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25121 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25121, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25122 q = 1) (hb : d231381 q = 1) : d234725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25122, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65175 (p : Pattern) (ha : d201977 p = 1) (hb : d231381 p = 1) : d234731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56746 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56747 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25123 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
    | true =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
  have h9 (q : Pattern) (ha : d201973 q = 1) (hb : d231381 q = 1) : d234727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201973, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d201974 q = 1) (hb : d231381 q = 1) : d234728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d234728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201974, d234728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201975 q = 1) (hb : d231381 q = 1) : d234729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d234729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201975, d234729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201976 q = 1) (hb : d231381 q = 1) : d234730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d234730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201976, d234730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d201977 q = 1) (hb : d231381 q = 1) : d234731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201977, d234731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201977, d234731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65176 (p : Pattern) (ha : d25129 p = 1) (hb : d231381 p = 1) : d234732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25121 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25121, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25129 q = 1) (hb : d231381 q = 1) : d234732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25129, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65177 (p : Pattern) (ha : d201982 p = 1) (hb : d231381 p = 1) : d234738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56746 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56747 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25123 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
    | true =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
  have h9 (q : Pattern) (ha : d201973 q = 1) (hb : d231381 q = 1) : d234727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201973, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d201974 q = 1) (hb : d231381 q = 1) : d234728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d234728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201974, d234728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201975 q = 1) (hb : d231381 q = 1) : d234729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d234729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201975, d234729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201976 q = 1) (hb : d231381 q = 1) : d234730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d234730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201976, d234730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56750 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56751 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25130 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65176 q ha hb
    | true =>
      simp only [d25130, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
  have h23 (q : Pattern) (ha : d201978 q = 1) (hb : d231381 q = 1) : d234734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d201978, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d201979 q = 1) (hb : d231381 q = 1) : d234735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d234735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d201979, d234735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d201980 q = 1) (hb : d231381 q = 1) : d234736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201980, d234736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d201980, d234736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d201981 q = 1) (hb : d231381 q = 1) : d234737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201981, d234737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d201981, d234737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d201982 q = 1) (hb : d231381 q = 1) : d234738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201982, d234738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d201982, d234738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro65178 (p : Pattern) (ha : d201989 p = 1) (hb : d231381 p = 1) : d234743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25130 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65176 q ha hb
    | true =>
      simp only [d25130, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
  have h2 (q : Pattern) (ha : d201978 q = 1) (hb : d231381 q = 1) : d234734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201978, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201979 q = 1) (hb : d231381 q = 1) : d234735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d234735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201979, d234735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201987 q = 1) (hb : d231381 q = 1) : d234736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201987, d234736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201987, d234736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201988 q = 1) (hb : d231381 q = 1) : d234737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201988, d234737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201988, d234737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201989 q = 1) (hb : d231381 q = 1) : d234743 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201989, d234743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201989, d234743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65179 (p : Pattern) (ha : d25153 p = 1) (hb : d231381 p = 1) : d234749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25148 q = 1) (hb : d231381 q = 1) : d29395 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65171 q ha hb
  have h2 (q : Pattern) (ha : d25105 q = 1) (hb : d231381 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65171 q ha hb
    | true =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25149 q = 1) (hb : d231381 q = 1) : d29396 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25149, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25106 q = 1) (hb : d231381 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25150 q = 1) (hb : d231381 q = 1) : d29397 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25150, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25151 q = 1) (hb : d231381 q = 1) : d29398 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25151, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25152 q = 1) (hb : d231381 q = 1) : d29399 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25152, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25153 q = 1) (hb : d231381 q = 1) : d234749 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d234749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25153, d234749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65180 (p : Pattern) (ha : d25159 p = 1) (hb : d231381 p = 1) : d234755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25154 q = 1) (hb : d231381 q = 1) : d234750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
    | true =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
  have h2 (q : Pattern) (ha : d25155 q = 1) (hb : d231381 q = 1) : d234751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25156 q = 1) (hb : d231381 q = 1) : d234752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25157 q = 1) (hb : d231381 q = 1) : d234753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25157, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25158 q = 1) (hb : d231381 q = 1) : d234754 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d234754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25158, d234754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25159 q = 1) (hb : d231381 q = 1) : d234755 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d234755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25159, d234755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro65181 (p : Pattern) (ha : d25165 p = 1) (hb : d231381 p = 1) : d234761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d231381 q = 1) : d234756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65180 q ha hb
    | true =>
      simp only [d25160, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d231381 q = 1) : d234757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56730 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25162 q = 1) (hb : d231381 q = 1) : d234758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25162, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25163 q = 1) (hb : d231381 q = 1) : d234759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25163, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25164 q = 1) (hb : d231381 q = 1) : d234760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25164, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25165 q = 1) (hb : d231381 q = 1) : d234761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25165, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65182 (p : Pattern) (ha : d201999 p = 1) (hb : d231381 p = 1) : d234767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25166 q = 1) (hb : d231381 q = 1) : d234762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65181 q ha hb
    | true =>
      simp only [d25166, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56731 q ha hb
  have h2 (q : Pattern) (ha : d201995 q = 1) (hb : d231381 q = 1) : d234763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201995, d234763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201995, d234763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56731 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201996 q = 1) (hb : d231381 q = 1) : d234764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201996, d234764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201996, d234764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201997 q = 1) (hb : d231381 q = 1) : d234765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201997, d234765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201997, d234765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201998 q = 1) (hb : d231381 q = 1) : d234766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201998, d234766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201998, d234766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201999 q = 1) (hb : d231381 q = 1) : d234767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201999, d234767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201999, d234767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65183 (p : Pattern) (ha : d202005 p = 1) (hb : d231381 p = 1) : d234773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56734 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56734 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56735 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201983 q = 1) (hb : d231381 q = 1) : d234739 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201983, d234739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65175 q ha hb
    | true =>
      simp only [d201983, d234739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65177 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56736 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d201984 q = 1) (hb : d231381 q = 1) : d234740 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201984, d234740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201984, d234740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201985 q = 1) (hb : d231381 q = 1) : d234741 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201985, d234741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201985, d234741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d201986 q = 1) (hb : d231381 q = 1) : d234742 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201986, d234742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201986, d234742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d201990 q = 1) (hb : d231381 q = 1) : d234744 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201990, d234744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201990, d234744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65178 q ha hb
  have h12 (q : Pattern) (ha : d201991 q = 1) (hb : d231381 q = 1) : d234745 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201991, d234745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201991, d234745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d201992 q = 1) (hb : d231381 q = 1) : d234746 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201992, d234746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201992, d234746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d201993 q = 1) (hb : d231381 q = 1) : d234747 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201993, d234747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201993, d234747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d201994 q = 1) (hb : d231381 q = 1) : d234748 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201994, d234748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201994, d234748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202000 q = 1) (hb : d231381 q = 1) : d234768 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202000, d234768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202000, d234768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65182 q ha hb
  have h17 (q : Pattern) (ha : d202001 q = 1) (hb : d231381 q = 1) : d234769 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202001, d234769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202001, d234769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d202002 q = 1) (hb : d231381 q = 1) : d234770 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202002, d234770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202002, d234770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d202003 q = 1) (hb : d231381 q = 1) : d234771 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202003, d234771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202003, d234771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d202004 q = 1) (hb : d231381 q = 1) : d234772 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202004, d234772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202004, d234772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202005 q = 1) (hb : d231381 q = 1) : d234773 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202005, d234773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202005, d234773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro65184 (p : Pattern) (ha : d25187 p = 1) (hb : d231381 p = 1) : d234783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
    | true =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d231381 q = 1) : d234779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d231381 q = 1) : d234780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d231381 q = 1) : d234781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d231381 q = 1) : d234782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25187 q = 1) (hb : d231381 q = 1) : d234783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d234783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d234783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65185 (p : Pattern) (ha : d25194 p = 1) (hb : d231381 p = 1) : d234790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
    | true =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d231381 q = 1) : d234779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d231381 q = 1) : d234780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d231381 q = 1) : d234781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d231381 q = 1) : d234782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25130 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65176 q ha hb
    | true =>
      simp only [d25130, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56726 q ha hb
  have h7 (q : Pattern) (ha : d25190 q = 1) (hb : d231381 q = 1) : d234786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25191 q = 1) (hb : d231381 q = 1) : d234787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25191, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25192 q = 1) (hb : d231381 q = 1) : d234788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25193 q = 1) (hb : d231381 q = 1) : d234789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25194 q = 1) (hb : d231381 q = 1) : d234790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d234790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25194, d234790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65186 (p : Pattern) (ha : d25296 p = 1) (hb : d231381 p = 1) : d234850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
    | true =>
      simp only [d25123, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d231381 q = 1) : d234779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d231381 q = 1) : d234780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d231381 q = 1) : d234781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d231381 q = 1) : d234782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56724 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25296 q = 1) (hb : d231381 q = 1) : d234850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d234850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25296, d234850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65187 (p : Pattern) (ha : d25199 p = 1) (hb : d231381 p = 1) : d234795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25198 q = 1) (hb : d231381 q = 1) : d234794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25199 q = 1) (hb : d231381 q = 1) : d234795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d234795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25199, d234795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65188 (p : Pattern) (ha : d25206 p = 1) (hb : d231381 p = 1) : d234802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25204 q = 1) (hb : d231381 q = 1) : d234800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25205 q = 1) (hb : d231381 q = 1) : d234801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25205, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25206 q = 1) (hb : d231381 q = 1) : d234802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d234802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25206, d234802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65189 (p : Pattern) (ha : d25213 p = 1) (hb : d231381 p = 1) : d234808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9796 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25211 q = 1) (hb : d231381 q = 1) : d234806 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d231381, d234806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25211, d231381, d234806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25212 q = 1) (hb : d231381 q = 1) : d234807 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d234807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25212, d234807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d152852 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25102 q = 1) (hb : d231381 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d231381, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d25102, d231381, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25103 q = 1) (hb : d231381 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25103, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25213 q = 1) (hb : d231381 q = 1) : d234808 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d234808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25213, d234808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro65190 (p : Pattern) (ha : d25221 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25219 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25219, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25220 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d22, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25221 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65191 (p : Pattern) (ha : d25227 p = 1) (hb : d231381 p = 1) : d235119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d231381 q = 1) : d234809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d234809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65189 q ha hb
    | true =>
      simp only [d25214, d234809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d231381 q = 1) : d234810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d234810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d234810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d231381 q = 1) : d234811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d234811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d234811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d231381 q = 1) : d234812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d234812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d234812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25105 q = 1) (hb : d231381 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65171 q ha hb
    | true =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25106 q = 1) (hb : d231381 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25107 q = 1) (hb : d231381 q = 1) : d29117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25108 q = 1) (hb : d231381 q = 1) : d29118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25108, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25218 q = 1) (hb : d231381 q = 1) : d234813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d234813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25218, d234813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25222 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
    | true =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25223 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25224 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25225 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25226 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25227 q = 1) (hb : d231381 q = 1) : d235119 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d235119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25227, d235119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65192 (p : Pattern) (ha : d25233 p = 1) (hb : d231381 p = 1) : d260562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d231381 q = 1) : d260557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d260557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65191 q ha hb
    | true =>
      simp only [d25228, d260557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d231381 q = 1) : d260558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d260558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d260558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d231381 q = 1) : d260559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d260559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d260559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25111 q = 1) (hb : d231381 q = 1) : d234714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
    | true =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
  have h5 (q : Pattern) (ha : d25112 q = 1) (hb : d231381 q = 1) : d234715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25113 q = 1) (hb : d231381 q = 1) : d234716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25231 q = 1) (hb : d231381 q = 1) : d260560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d260560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d260560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25114 q = 1) (hb : d231381 q = 1) : d234717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25114, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25232 q = 1) (hb : d231381 q = 1) : d260561 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d260561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25232, d260561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25233 q = 1) (hb : d231381 q = 1) : d260562 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d260562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25233, d260562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro65193 (p : Pattern) (ha : d25239 p = 1) (hb : d231381 p = 1) : d260568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65192 q ha hb
    | true =>
      simp only [d25234, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d231381 q = 1) : d260566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d231381 q = 1) : d260567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25239 q = 1) (hb : d231381 q = 1) : d260568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d260568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25239, d260568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65194 (p : Pattern) (ha : d25267 p = 1) (hb : d231381 p = 1) : d234725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25267 q = 1) (hb : d231381 q = 1) : d234725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25267, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65195 (p : Pattern) (ha : d202015 p = 1) (hb : d231381 p = 1) : d260574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25200 q = 1) (hb : d231381 q = 1) : d234796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d234796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65187 q ha hb
    | true =>
      simp only [d25200, d234796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56746 q ha hb
  have h2 (q : Pattern) (ha : d25201 q = 1) (hb : d231381 q = 1) : d234797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d234797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d234797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25202 q = 1) (hb : d231381 q = 1) : d234798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d234798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25202, d234798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25203 q = 1) (hb : d231381 q = 1) : d234799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d234799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d234799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25207 q = 1) (hb : d231381 q = 1) : d234803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d234803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65188 q ha hb
    | true =>
      simp only [d25207, d234803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56747 q ha hb
  have h6 (q : Pattern) (ha : d25208 q = 1) (hb : d231381 q = 1) : d234804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d234804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d234804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25209 q = 1) (hb : d231381 q = 1) : d234805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d234805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25209, d234805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25240 q = 1) (hb : d231381 q = 1) : d260569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65193 q ha hb
    | true =>
      simp only [d25240, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
  have h9 (q : Pattern) (ha : d202011 q = 1) (hb : d231381 q = 1) : d260570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d260570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202011, d260570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25268 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65194 q ha hb
    | true =>
      simp only [d25268, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25269 q = 1) (hb : d231381 q = 1) : d234727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25269, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202012 q = 1) (hb : d231381 q = 1) : d260571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d260571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202012, d260571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202013 q = 1) (hb : d231381 q = 1) : d260572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d260572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202013, d260572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202014 q = 1) (hb : d231381 q = 1) : d260573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d260573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202014, d260573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202015 q = 1) (hb : d231381 q = 1) : d260574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d260574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202015, d260574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65196 (p : Pattern) (ha : d25274 p = 1) (hb : d231381 p = 1) : d234833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25198 q = 1) (hb : d231381 q = 1) : d234794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25274 q = 1) (hb : d231381 q = 1) : d234833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d234833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25274, d234833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65197 (p : Pattern) (ha : d25279 p = 1) (hb : d231381 p = 1) : d234838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56723 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25204 q = 1) (hb : d231381 q = 1) : d234800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25205 q = 1) (hb : d231381 q = 1) : d234801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25205, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25279 q = 1) (hb : d231381 q = 1) : d234838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d234838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25279, d234838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65198 (p : Pattern) (ha : d25283 p = 1) (hb : d231381 p = 1) : d260575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65192 q ha hb
    | true =>
      simp only [d25234, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d231381 q = 1) : d260566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d231381 q = 1) : d260567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25283 q = 1) (hb : d231381 q = 1) : d260575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d260575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25283, d260575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65199 (p : Pattern) (ha : d25288 p = 1) (hb : d231381 p = 1) : d234732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65173 q ha hb
    | true =>
      simp only [d25117, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25288 q = 1) (hb : d231381 q = 1) : d234732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25288, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65200 (p : Pattern) (ha : d202020 p = 1) (hb : d231381 p = 1) : d260581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25200 q = 1) (hb : d231381 q = 1) : d234796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d234796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65187 q ha hb
    | true =>
      simp only [d25200, d234796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56746 q ha hb
  have h2 (q : Pattern) (ha : d25201 q = 1) (hb : d231381 q = 1) : d234797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d234797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d234797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25202 q = 1) (hb : d231381 q = 1) : d234798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d234798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25202, d234798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25203 q = 1) (hb : d231381 q = 1) : d234799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d234799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d234799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25207 q = 1) (hb : d231381 q = 1) : d234803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d234803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65188 q ha hb
    | true =>
      simp only [d25207, d234803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56747 q ha hb
  have h6 (q : Pattern) (ha : d25208 q = 1) (hb : d231381 q = 1) : d234804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d234804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d234804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25209 q = 1) (hb : d231381 q = 1) : d234805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d234805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25209, d234805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25240 q = 1) (hb : d231381 q = 1) : d260569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65193 q ha hb
    | true =>
      simp only [d25240, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65174 q ha hb
  have h9 (q : Pattern) (ha : d202011 q = 1) (hb : d231381 q = 1) : d260570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d260570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202011, d260570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25268 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65194 q ha hb
    | true =>
      simp only [d25268, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25269 q = 1) (hb : d231381 q = 1) : d234727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25269, d234727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202012 q = 1) (hb : d231381 q = 1) : d260571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d260571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202012, d260571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202013 q = 1) (hb : d231381 q = 1) : d260572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d260572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202013, d260572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202014 q = 1) (hb : d231381 q = 1) : d260573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d260573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202014, d260573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25275 q = 1) (hb : d231381 q = 1) : d234834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d234834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65196 q ha hb
    | true =>
      simp only [d25275, d234834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56750 q ha hb
  have h16 (q : Pattern) (ha : d25276 q = 1) (hb : d231381 q = 1) : d234835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d234835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25276, d234835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25277 q = 1) (hb : d231381 q = 1) : d234836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d234836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25277, d234836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25278 q = 1) (hb : d231381 q = 1) : d234837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d234837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25278, d234837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25280 q = 1) (hb : d231381 q = 1) : d234839 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d234839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65197 q ha hb
    | true =>
      simp only [d25280, d234839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56751 q ha hb
  have h20 (q : Pattern) (ha : d25281 q = 1) (hb : d231381 q = 1) : d234840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d234840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25281, d234840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25282 q = 1) (hb : d231381 q = 1) : d234841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d234841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25282, d234841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25284 q = 1) (hb : d231381 q = 1) : d260576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d260576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65198 q ha hb
    | true =>
      simp only [d25284, d260576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65176 q ha hb
  have h23 (q : Pattern) (ha : d202016 q = 1) (hb : d231381 q = 1) : d260577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d260577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202016, d260577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25289 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65199 q ha hb
    | true =>
      simp only [d25289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25290 q = 1) (hb : d231381 q = 1) : d234734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25290, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202017 q = 1) (hb : d231381 q = 1) : d260578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d260578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202017, d260578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202018 q = 1) (hb : d231381 q = 1) : d260579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d260579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202018, d260579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202019 q = 1) (hb : d231381 q = 1) : d260580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d260580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202019, d260580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202020 q = 1) (hb : d231381 q = 1) : d260581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d260581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202020, d260581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro65201 (p : Pattern) (ha : d202027 p = 1) (hb : d231381 p = 1) : d260588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25284 q = 1) (hb : d231381 q = 1) : d260576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d260576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65198 q ha hb
    | true =>
      simp only [d25284, d260576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65176 q ha hb
  have h2 (q : Pattern) (ha : d202016 q = 1) (hb : d231381 q = 1) : d260577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d260577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202016, d260577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25289 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65199 q ha hb
    | true =>
      simp only [d25289, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25290 q = 1) (hb : d231381 q = 1) : d234734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25290, d234734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202017 q = 1) (hb : d231381 q = 1) : d260578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d260578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202017, d260578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202025 q = 1) (hb : d231381 q = 1) : d260586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d260586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202025, d260586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202026 q = 1) (hb : d231381 q = 1) : d260587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d260587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202026, d260587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d231381 q = 1) : d260588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d260588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d260588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65202 (p : Pattern) (ha : d25319 p = 1) (hb : d231381 p = 1) : d235219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d231381 q = 1) : d234863 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d234863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d234863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65189 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d231381 q = 1) : d234809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d234809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65189 q ha hb
    | true =>
      simp only [d25214, d234809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d231381 q = 1) : d234864 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d234864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d234864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d231381 q = 1) : d234810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d234810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d234810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d231381 q = 1) : d234865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d234865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d234865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d231381 q = 1) : d234866 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d234866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d234866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25148 q = 1) (hb : d231381 q = 1) : d29395 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65171 q ha hb
  have h8 (q : Pattern) (ha : d25105 q = 1) (hb : d231381 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65171 q ha hb
    | true =>
      simp only [d25105, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25149 q = 1) (hb : d231381 q = 1) : d29396 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25149, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25106 q = 1) (hb : d231381 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25106, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25150 q = 1) (hb : d231381 q = 1) : d29397 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25150, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25151 q = 1) (hb : d231381 q = 1) : d29398 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25151, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25313 q = 1) (hb : d231381 q = 1) : d234867 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d234867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25313, d234867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25314 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
  have h15 (q : Pattern) (ha : d25222 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
    | true =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25315 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25223 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25316 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25317 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25318 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25319 q = 1) (hb : d231381 q = 1) : d235219 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d235219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25319, d235219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro65203 (p : Pattern) (ha : d25325 p = 1) (hb : d231381 p = 1) : d260599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d231381 q = 1) : d260594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d260594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65202 q ha hb
    | true =>
      simp only [d25320, d260594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d231381 q = 1) : d260595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d260595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d260595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d231381 q = 1) : d260596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d260596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d260596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25154 q = 1) (hb : d231381 q = 1) : d234750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
    | true =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
  have h5 (q : Pattern) (ha : d25155 q = 1) (hb : d231381 q = 1) : d234751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25156 q = 1) (hb : d231381 q = 1) : d234752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25323 q = 1) (hb : d231381 q = 1) : d260597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d260597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d260597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25157 q = 1) (hb : d231381 q = 1) : d234753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25157, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25324 q = 1) (hb : d231381 q = 1) : d260598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d260598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25324, d260598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25325 q = 1) (hb : d231381 q = 1) : d260599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d260599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25325, d260599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro65204 (p : Pattern) (ha : d25331 p = 1) (hb : d231381 p = 1) : d260605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25326 q = 1) (hb : d231381 q = 1) : d260600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d260600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65203 q ha hb
    | true =>
      simp only [d25326, d260600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25327 q = 1) (hb : d231381 q = 1) : d260601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d260601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25327, d260601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25160 q = 1) (hb : d231381 q = 1) : d234756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65180 q ha hb
    | true =>
      simp only [d25160, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25161 q = 1) (hb : d231381 q = 1) : d234757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25328 q = 1) (hb : d231381 q = 1) : d260602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d260602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25328, d260602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25329 q = 1) (hb : d231381 q = 1) : d260603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d260603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25329, d260603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25330 q = 1) (hb : d231381 q = 1) : d260604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d260604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25330, d260604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25331 q = 1) (hb : d231381 q = 1) : d260605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d260605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25331, d260605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65205 (p : Pattern) (ha : d25356 p = 1) (hb : d231381 p = 1) : d234761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d231381 q = 1) : d234756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65180 q ha hb
    | true =>
      simp only [d25160, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d231381 q = 1) : d234757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25353 q = 1) (hb : d231381 q = 1) : d234758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25353, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25354 q = 1) (hb : d231381 q = 1) : d234759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25354, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25355 q = 1) (hb : d231381 q = 1) : d234760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25355, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25356 q = 1) (hb : d231381 q = 1) : d234761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25356, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65206 (p : Pattern) (ha : d202037 p = 1) (hb : d231381 p = 1) : d260611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25332 q = 1) (hb : d231381 q = 1) : d260606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d260606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65204 q ha hb
    | true =>
      simp only [d25332, d260606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65181 q ha hb
  have h2 (q : Pattern) (ha : d202033 q = 1) (hb : d231381 q = 1) : d260607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d260607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202033, d260607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25357 q = 1) (hb : d231381 q = 1) : d234762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65205 q ha hb
    | true =>
      simp only [d25357, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25358 q = 1) (hb : d231381 q = 1) : d234763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d234763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25358, d234763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d231381 q = 1) : d260608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d260608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202034, d260608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d231381 q = 1) : d260609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d260609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d260609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d231381 q = 1) : d260610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d260610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d260610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d231381 q = 1) : d260611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d260611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d260611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65207 (p : Pattern) (ha : d202043 p = 1) (hb : d231381 p = 1) : d260617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25188 q = 1) (hb : d231381 q = 1) : d234784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d234784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25188, d234784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65184 q ha hb
  have h2 (q : Pattern) (ha : d25189 q = 1) (hb : d231381 q = 1) : d234785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d234785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25189, d234785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25195 q = 1) (hb : d231381 q = 1) : d234791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d234791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65184 q ha hb
    | true =>
      simp only [d25195, d234791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65185 q ha hb
  have h4 (q : Pattern) (ha : d25196 q = 1) (hb : d231381 q = 1) : d234792 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d234792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25196, d234792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25197 q = 1) (hb : d231381 q = 1) : d234793 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d234793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25197, d234793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202021 q = 1) (hb : d231381 q = 1) : d260582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d260582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65195 q ha hb
    | true =>
      simp only [d202021, d260582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65200 q ha hb
  have h7 (q : Pattern) (ha : d25297 q = 1) (hb : d231381 q = 1) : d234851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d234851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65186 q ha hb
    | true =>
      simp only [d25297, d234851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56735 q ha hb
  have h8 (q : Pattern) (ha : d202022 q = 1) (hb : d231381 q = 1) : d260583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d260583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202022, d260583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202023 q = 1) (hb : d231381 q = 1) : d260584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d260584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202023, d260584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202024 q = 1) (hb : d231381 q = 1) : d260585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d260585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202024, d260585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202028 q = 1) (hb : d231381 q = 1) : d260589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d260589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202028, d260589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65201 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56757 q ha hb
  have h13 (q : Pattern) (ha : d202029 q = 1) (hb : d231381 q = 1) : d260590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d260590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202029, d260590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202030 q = 1) (hb : d231381 q = 1) : d260591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d260591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202030, d260591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202031 q = 1) (hb : d231381 q = 1) : d260592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d260592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202031, d260592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202032 q = 1) (hb : d231381 q = 1) : d260593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d260593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202032, d260593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202038 q = 1) (hb : d231381 q = 1) : d260612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d260612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202038, d260612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65206 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56758 q ha hb
  have h19 (q : Pattern) (ha : d202039 q = 1) (hb : d231381 q = 1) : d260613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d260613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202039, d260613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202040 q = 1) (hb : d231381 q = 1) : d260614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d260614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202040, d260614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202041 q = 1) (hb : d231381 q = 1) : d260615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d260615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202041, d260615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202042 q = 1) (hb : d231381 q = 1) : d260616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d260616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202042, d260616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202043 q = 1) (hb : d231381 q = 1) : d260617 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d260617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202043, d260617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro65208 (p : Pattern) (ha : d202049 p = 1) (hb : d231381 p = 1) : d260623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56733 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202006 q = 1) (hb : d231381 q = 1) : d234774 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202006, d234774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202006, d234774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65183 q ha hb
  have h6 (q : Pattern) (ha : d202007 q = 1) (hb : d231381 q = 1) : d234775 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202007, d234775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202007, d234775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202008 q = 1) (hb : d231381 q = 1) : d234776 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202008, d234776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202008, d234776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202009 q = 1) (hb : d231381 q = 1) : d234777 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202009, d234777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202009, d234777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202010 q = 1) (hb : d231381 q = 1) : d234778 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202010, d234778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202010, d234778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202044 q = 1) (hb : d231381 q = 1) : d260618 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d260618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202044, d260618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65207 q ha hb
  have h11 (q : Pattern) (ha : d202045 q = 1) (hb : d231381 q = 1) : d260619 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d260619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202045, d260619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202046 q = 1) (hb : d231381 q = 1) : d260620 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d260620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202046, d260620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202047 q = 1) (hb : d231381 q = 1) : d260621 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d260621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202047, d260621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202048 q = 1) (hb : d231381 q = 1) : d260622 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d260622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202048, d260622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202049 q = 1) (hb : d231381 q = 1) : d260623 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d260623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202049, d260623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65209 (p : Pattern) (ha : d25377 p = 1) (hb : d231381 p = 1) : d260562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d231381 q = 1) : d260557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d260557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65191 q ha hb
    | true =>
      simp only [d25228, d260557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d231381 q = 1) : d260558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d260558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d260558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d231381 q = 1) : d260559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d260559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d260559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25111 q = 1) (hb : d231381 q = 1) : d234714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
    | true =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
  have h5 (q : Pattern) (ha : d25112 q = 1) (hb : d231381 q = 1) : d234715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25113 q = 1) (hb : d231381 q = 1) : d234716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25231 q = 1) (hb : d231381 q = 1) : d260560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d260560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d260560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25375 q = 1) (hb : d231381 q = 1) : d234717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25375, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25376 q = 1) (hb : d231381 q = 1) : d260561 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d260561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25376, d260561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25377 q = 1) (hb : d231381 q = 1) : d260562 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d260562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25377, d260562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro65210 (p : Pattern) (ha : d25381 p = 1) (hb : d231381 p = 1) : d234719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25111 q = 1) (hb : d231381 q = 1) : d234714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
    | true =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
  have h2 (q : Pattern) (ha : d25112 q = 1) (hb : d231381 q = 1) : d234715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25113 q = 1) (hb : d231381 q = 1) : d234716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25375 q = 1) (hb : d231381 q = 1) : d234717 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25375, d234717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25380 q = 1) (hb : d231381 q = 1) : d234718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d234718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25380, d234718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25381 q = 1) (hb : d231381 q = 1) : d234719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d234719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25381, d234719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65211 (p : Pattern) (ha : d25387 p = 1) (hb : d231381 p = 1) : d260568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d231381 q = 1) : d260566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d231381 q = 1) : d260567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25387 q = 1) (hb : d231381 q = 1) : d260568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d260568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25387, d260568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65212 (p : Pattern) (ha : d25391 p = 1) (hb : d231381 p = 1) : d234725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25391 q = 1) (hb : d231381 q = 1) : d234725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25391, d234725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65213 (p : Pattern) (ha : d25397 p = 1) (hb : d231381 p = 1) : d260628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d231381 q = 1) : d260569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65211 q ha hb
    | true =>
      simp only [d25392, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65212 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d231381 q = 1) : d260624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d260624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d260624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d231381 q = 1) : d260625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d260625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d260625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d231381 q = 1) : d260626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d260626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d260626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d231381 q = 1) : d260627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d260627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d260627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25397 q = 1) (hb : d231381 q = 1) : d260628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d260628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25397, d260628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65214 (p : Pattern) (ha : d25400 p = 1) (hb : d231381 p = 1) : d260575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d231381 q = 1) : d260566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d231381 q = 1) : d260567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d260567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25400 q = 1) (hb : d231381 q = 1) : d260575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d260575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25400, d260575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65215 (p : Pattern) (ha : d25401 p = 1) (hb : d231381 p = 1) : d234732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d231381 q = 1) : d234724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d234724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25401 q = 1) (hb : d231381 q = 1) : d234732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25401, d234732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65216 (p : Pattern) (ha : d25407 p = 1) (hb : d231381 p = 1) : d260635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d231381 q = 1) : d260569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65211 q ha hb
    | true =>
      simp only [d25392, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65212 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d231381 q = 1) : d260624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d260624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d260624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d231381 q = 1) : d260625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d260625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d260625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d231381 q = 1) : d260626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d260626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d260626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d231381 q = 1) : d260627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d260627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d260627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25402 q = 1) (hb : d231381 q = 1) : d260576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d260576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65214 q ha hb
    | true =>
      simp only [d25402, d260576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65215 q ha hb
  have h7 (q : Pattern) (ha : d25403 q = 1) (hb : d231381 q = 1) : d260631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d260631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d260631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25404 q = 1) (hb : d231381 q = 1) : d260632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d260632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25404, d260632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25405 q = 1) (hb : d231381 q = 1) : d260633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d260633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d260633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25406 q = 1) (hb : d231381 q = 1) : d260634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d260634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d260634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25407 q = 1) (hb : d231381 q = 1) : d260635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d260635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25407, d260635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65217 (p : Pattern) (ha : d25556 p = 1) (hb : d231381 p = 1) : d260707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d231381 q = 1) : d260569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65211 q ha hb
    | true =>
      simp only [d25392, d260569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65212 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d231381 q = 1) : d260624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d260624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d260624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d231381 q = 1) : d260625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d260625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d260625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d231381 q = 1) : d260626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d260626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d260626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d231381 q = 1) : d260627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d260627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d260627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25551 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65212 q ha hb
    | true =>
      simp only [d25551, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25552 q = 1) (hb : d231381 q = 1) : d234779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25553 q = 1) (hb : d231381 q = 1) : d234780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25553, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25554 q = 1) (hb : d231381 q = 1) : d234781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25555 q = 1) (hb : d231381 q = 1) : d234782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25556 q = 1) (hb : d231381 q = 1) : d260707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25556, d260707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25556, d260707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65218 (p : Pattern) (ha : d25562 p = 1) (hb : d231381 p = 1) : d234790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25551 q = 1) (hb : d231381 q = 1) : d234726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65212 q ha hb
    | true =>
      simp only [d25551, d234726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25552 q = 1) (hb : d231381 q = 1) : d234779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d234779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25553 q = 1) (hb : d231381 q = 1) : d234780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25553, d234780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25554 q = 1) (hb : d231381 q = 1) : d234781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d234781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25555 q = 1) (hb : d231381 q = 1) : d234782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d234782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25557 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65215 q ha hb
    | true =>
      simp only [d25557, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25558 q = 1) (hb : d231381 q = 1) : d234786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25559 q = 1) (hb : d231381 q = 1) : d234787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25559, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25560 q = 1) (hb : d231381 q = 1) : d234788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25561 q = 1) (hb : d231381 q = 1) : d234789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25562 q = 1) (hb : d231381 q = 1) : d234790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25562, d234790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25562, d234790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65219 (p : Pattern) (ha : d25571 p = 1) (hb : d231381 p = 1) : d234988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25557 q = 1) (hb : d231381 q = 1) : d234733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65215 q ha hb
    | true =>
      simp only [d25557, d234733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25558 q = 1) (hb : d231381 q = 1) : d234786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d234786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25559 q = 1) (hb : d231381 q = 1) : d234787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25559, d234787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25560 q = 1) (hb : d231381 q = 1) : d234788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d234788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25561 q = 1) (hb : d231381 q = 1) : d234789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d234789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25571 q = 1) (hb : d231381 q = 1) : d234988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25571, d234988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25571, d234988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65220 (p : Pattern) (ha : d25614 p = 1) (hb : d231381 p = 1) : d234755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25154 q = 1) (hb : d231381 q = 1) : d234750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
    | true =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
  have h2 (q : Pattern) (ha : d25155 q = 1) (hb : d231381 q = 1) : d234751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25156 q = 1) (hb : d231381 q = 1) : d234752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25604 q = 1) (hb : d231381 q = 1) : d234753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25604, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25613 q = 1) (hb : d231381 q = 1) : d234754 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25613, d234754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25613, d234754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25614 q = 1) (hb : d231381 q = 1) : d234755 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25614, d234755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25614, d234755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65221 (p : Pattern) (ha : d25670 p = 1) (hb : d231381 p = 1) : d234761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25615 q = 1) (hb : d231381 q = 1) : d234756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65220 q ha hb
    | true =>
      simp only [d25615, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25616 q = 1) (hb : d231381 q = 1) : d234757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25667 q = 1) (hb : d231381 q = 1) : d234758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25667, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25667, d234758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25668 q = 1) (hb : d231381 q = 1) : d234759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25668, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25668, d234759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25669 q = 1) (hb : d231381 q = 1) : d234760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25669, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25669, d234760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25670 q = 1) (hb : d231381 q = 1) : d234761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25670, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25670, d234761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65222 (p : Pattern) (ha : d25676 p = 1) (hb : d231381 p = 1) : d235029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25671 q = 1) (hb : d231381 q = 1) : d234762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25671, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65221 q ha hb
    | true =>
      simp only [d25671, d234762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25672 q = 1) (hb : d231381 q = 1) : d235025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25672, d235025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25672, d235025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25673 q = 1) (hb : d231381 q = 1) : d235026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25673, d235026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25673, d235026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25674 q = 1) (hb : d231381 q = 1) : d235027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25674, d235027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25674, d235027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25675 q = 1) (hb : d231381 q = 1) : d235028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25675, d235028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25675, d235028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25676 q = 1) (hb : d231381 q = 1) : d235029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25676, d235029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25676, d235029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65223 (p : Pattern) (ha : d25412 p = 1) (hb : d231381 p = 1) : d260640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d231381 q = 1) : d260566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d231381 q = 1) : d260639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d260639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d260639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25412 q = 1) (hb : d231381 q = 1) : d260640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d260640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25412, d260640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65224 (p : Pattern) (ha : d25414 p = 1) (hb : d231381 p = 1) : d234795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d231381 q = 1) : d234794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25414 q = 1) (hb : d231381 q = 1) : d234795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d234795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25414, d234795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65225 (p : Pattern) (ha : d25421 p = 1) (hb : d231381 p = 1) : d260647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d231381 q = 1) : d260645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d260645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d260645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d231381 q = 1) : d260646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d260646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d260646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25421 q = 1) (hb : d231381 q = 1) : d260647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d260647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25421, d260647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65226 (p : Pattern) (ha : d25424 p = 1) (hb : d231381 p = 1) : d234802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d231381 q = 1) : d234800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d231381 q = 1) : d234801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25424 q = 1) (hb : d231381 q = 1) : d234802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d234802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25424, d234802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65227 (p : Pattern) (ha : d25438 p = 1) (hb : d231381 p = 1) : d260651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25428 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25429 q = 1) (hb : d152852 q = 1) : d25429 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25430 q = 1) (hb : d231381 q = 1) : d234926 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d231381, d234926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25430, d231381, d234926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25431 q = 1) (hb : d231381 q = 1) : d234927 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d234927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25431, d234927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25210 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25435 q = 1) (hb : d152852 q = 1) : d25435 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25436 q = 1) (hb : d231381 q = 1) : d249803 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25436, d231381, d249803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d25436, d231381, d249803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25437 q = 1) (hb : d231381 q = 1) : d249804 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25437, d249804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25437, d249804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25438 q = 1) (hb : d231381 q = 1) : d260651 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d260651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25438, d260651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro65228 (p : Pattern) (ha : d25443 p = 1) (hb : d231381 p = 1) : d260656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9796 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25211 q = 1) (hb : d231381 q = 1) : d234806 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d231381, d234806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25211, d231381, d234806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25212 q = 1) (hb : d231381 q = 1) : d234807 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d234807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25212, d234807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25219 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d25219, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25220 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25443 q = 1) (hb : d231381 q = 1) : d260656 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d260656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25443, d260656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro65229 (p : Pattern) (ha : d25451 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25449 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25449, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25450 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25219 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d25219, d231381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d25220 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25451 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65230 (p : Pattern) (ha : d25457 p = 1) (hb : d231381 p = 1) : d260662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d231381 q = 1) : d260652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d260652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65227 q ha hb
    | true =>
      simp only [d25439, d260652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d231381 q = 1) : d260653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d260653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d260653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d231381 q = 1) : d260654 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d260654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d260654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d231381 q = 1) : d260655 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d260655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d260655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d231381 q = 1) : d260657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d260657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65228 q ha hb
    | true =>
      simp only [d25444, d260657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d231381 q = 1) : d260658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d260658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d260658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d231381 q = 1) : d260659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d260659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d260659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d231381 q = 1) : d260660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d260660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d260660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d231381 q = 1) : d260661 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d260661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d260661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25452 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65229 q ha hb
    | true =>
      simp only [d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25453 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25454 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25455 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25222 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
    | true =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25223 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25224 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25225 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25456 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25457 q = 1) (hb : d231381 q = 1) : d260662 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d260662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25457, d260662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro65231 (p : Pattern) (ha : d25461 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25222 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
    | true =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25223 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25224 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25225 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25226 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25461 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro65232 (p : Pattern) (ha : d25467 p = 1) (hb : d231381 p = 1) : d260668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25458 q = 1) (hb : d231381 q = 1) : d260663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d260663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65230 q ha hb
    | true =>
      simp only [d25458, d260663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65191 q ha hb
  have h2 (q : Pattern) (ha : d25459 q = 1) (hb : d231381 q = 1) : d260664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d260664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25459, d260664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25460 q = 1) (hb : d231381 q = 1) : d260665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d260665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25460, d260665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25462 q = 1) (hb : d231381 q = 1) : d235120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d235120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65191 q ha hb
    | true =>
      simp only [d25462, d235120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65231 q ha hb
  have h5 (q : Pattern) (ha : d25463 q = 1) (hb : d231381 q = 1) : d235121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d235121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25463, d235121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25464 q = 1) (hb : d231381 q = 1) : d235122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d235122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25464, d235122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25465 q = 1) (hb : d231381 q = 1) : d260666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d260666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25465, d260666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25228 q = 1) (hb : d231381 q = 1) : d260557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d260557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65191 q ha hb
    | true =>
      simp only [d25228, d260557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
  have h9 (q : Pattern) (ha : d25229 q = 1) (hb : d231381 q = 1) : d260558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d260558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d260558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25230 q = 1) (hb : d231381 q = 1) : d260559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d260559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d260559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25111 q = 1) (hb : d231381 q = 1) : d234714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65172 q ha hb
    | true =>
      simp only [d25111, d234714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56722 q ha hb
  have h12 (q : Pattern) (ha : d25112 q = 1) (hb : d231381 q = 1) : d234715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d234715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25113 q = 1) (hb : d231381 q = 1) : d234716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d234716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25231 q = 1) (hb : d231381 q = 1) : d260560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d260560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25231, d260560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25466 q = 1) (hb : d231381 q = 1) : d260667 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d260667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25466, d260667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25467 q = 1) (hb : d231381 q = 1) : d260668 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d260668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25467, d260668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro65233 (p : Pattern) (ha : d25473 p = 1) (hb : d231381 p = 1) : d260674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d231381 q = 1) : d260669 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d260669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65232 q ha hb
    | true =>
      simp only [d25468, d260669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d231381 q = 1) : d260670 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d260670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d260670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d231381 q = 1) : d260671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d260671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d260671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d231381 q = 1) : d260672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d260672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d260672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d231381 q = 1) : d260673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d260673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d260673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25473 q = 1) (hb : d231381 q = 1) : d260674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d260674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25473, d260674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65234 (p : Pattern) (ha : d25519 p = 1) (hb : d231381 p = 1) : d260680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d231381 q = 1) : d260677 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d260677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d260677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d231381 q = 1) : d260678 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d260678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d260678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d231381 q = 1) : d260679 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d260679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d260679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25519 q = 1) (hb : d231381 q = 1) : d260680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25519, d260680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25519, d260680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro65235 (p : Pattern) (ha : d202054 p = 1) (hb : d231381 p = 1) : d260686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d231381 q = 1) : d260641 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d260641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65223 q ha hb
    | true =>
      simp only [d25415, d260641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65224 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d231381 q = 1) : d260642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d260642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d260642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d231381 q = 1) : d260643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d260643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d260643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d231381 q = 1) : d260644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d260644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d260644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d231381 q = 1) : d260648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d260648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65225 q ha hb
    | true =>
      simp only [d25425, d260648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65226 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d231381 q = 1) : d260649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d260649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d260649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d231381 q = 1) : d260650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d260650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d260650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d231381 q = 1) : d260675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d260675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65233 q ha hb
    | true =>
      simp only [d25474, d260675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65211 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d231381 q = 1) : d260676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d260676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d260676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d231381 q = 1) : d260681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d260681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65234 q ha hb
    | true =>
      simp only [d25520, d260681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d231381 q = 1) : d260682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d260682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d260682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d231381 q = 1) : d260683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d260683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d260683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d231381 q = 1) : d260684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d260684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d260684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d231381 q = 1) : d260685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d260685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d260685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202054 q = 1) (hb : d231381 q = 1) : d260686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d260686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d260686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65236 (p : Pattern) (ha : d25526 p = 1) (hb : d231381 p = 1) : d260687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d231381 q = 1) : d260566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d260566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d231381 q = 1) : d260639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d260639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d260639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25526 q = 1) (hb : d231381 q = 1) : d260687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25526, d260687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25526, d260687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65237 (p : Pattern) (ha : d25527 p = 1) (hb : d231381 p = 1) : d234833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d231381 q = 1) : d234723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d234723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d231381 q = 1) : d234794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d234794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25527 q = 1) (hb : d231381 q = 1) : d234833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25527, d234833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25527, d234833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65238 (p : Pattern) (ha : d25532 p = 1) (hb : d231381 p = 1) : d260692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d231381 q = 1) : d260565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d260565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d231381 q = 1) : d260645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d260645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d260645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d231381 q = 1) : d260646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d260646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d260646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25532 q = 1) (hb : d231381 q = 1) : d260692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25532, d260692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25532, d260692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65239 (p : Pattern) (ha : d25533 p = 1) (hb : d231381 p = 1) : d234838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d231381 q = 1) : d234720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65210 q ha hb
    | true =>
      simp only [d25382, d234720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d231381 q = 1) : d234721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d234721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d231381 q = 1) : d234722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d234722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d231381 q = 1) : d234800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d234800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d231381 q = 1) : d234801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d234801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25533 q = 1) (hb : d231381 q = 1) : d234838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25533, d234838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25533, d234838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65240 (p : Pattern) (ha : d25537 p = 1) (hb : d231381 p = 1) : d260696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d231381 q = 1) : d260669 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d260669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65232 q ha hb
    | true =>
      simp only [d25468, d260669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d231381 q = 1) : d260670 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d260670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d260670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d231381 q = 1) : d260671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d260671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d260671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d231381 q = 1) : d260672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d260672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d260672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d231381 q = 1) : d260673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d260673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d260673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25537 q = 1) (hb : d231381 q = 1) : d260696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25537, d260696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25537, d260696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65241 (p : Pattern) (ha : d25543 p = 1) (hb : d231381 p = 1) : d260699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d231381 q = 1) : d260563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65209 q ha hb
    | true =>
      simp only [d25378, d260563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d231381 q = 1) : d260564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d260564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d231381 q = 1) : d260677 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d260677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d260677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d231381 q = 1) : d260678 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d260678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d260678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d231381 q = 1) : d260679 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d260679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d260679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25543 q = 1) (hb : d231381 q = 1) : d260699 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25543, d260699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25543, d260699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro65242 (p : Pattern) (ha : d202059 p = 1) (hb : d231381 p = 1) : d260705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d231381 q = 1) : d260641 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d260641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65223 q ha hb
    | true =>
      simp only [d25415, d260641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65224 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d231381 q = 1) : d260642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d260642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d260642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d231381 q = 1) : d260643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d260643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d260643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d231381 q = 1) : d260644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d260644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d260644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d231381 q = 1) : d260648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d260648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65225 q ha hb
    | true =>
      simp only [d25425, d260648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65226 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d231381 q = 1) : d260649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d260649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d260649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d231381 q = 1) : d260650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d260650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d260650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d231381 q = 1) : d260675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d260675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65233 q ha hb
    | true =>
      simp only [d25474, d260675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65211 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d231381 q = 1) : d260676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d260676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d260676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d231381 q = 1) : d260681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d260681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65234 q ha hb
    | true =>
      simp only [d25520, d260681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d231381 q = 1) : d260682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d260682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d260682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d231381 q = 1) : d260683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d260683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d260683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d231381 q = 1) : d260684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d260684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d260684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d231381 q = 1) : d260685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d260685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d260685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25528 q = 1) (hb : d231381 q = 1) : d260688 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25528, d260688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65236 q ha hb
    | true =>
      simp only [d25528, d260688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65237 q ha hb
  have h16 (q : Pattern) (ha : d25529 q = 1) (hb : d231381 q = 1) : d260689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25529, d260689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25529, d260689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25530 q = 1) (hb : d231381 q = 1) : d260690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25530, d260690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25530, d260690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25531 q = 1) (hb : d231381 q = 1) : d260691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25531, d260691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25531, d260691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25534 q = 1) (hb : d231381 q = 1) : d260693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25534, d260693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65238 q ha hb
    | true =>
      simp only [d25534, d260693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65239 q ha hb
  have h20 (q : Pattern) (ha : d25535 q = 1) (hb : d231381 q = 1) : d260694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25535, d260694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25535, d260694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25536 q = 1) (hb : d231381 q = 1) : d260695 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25536, d260695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25536, d260695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25538 q = 1) (hb : d231381 q = 1) : d260697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d260697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65240 q ha hb
    | true =>
      simp only [d25538, d260697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65214 q ha hb
  have h23 (q : Pattern) (ha : d202055 q = 1) (hb : d231381 q = 1) : d260698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d260698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202055, d260698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25544 q = 1) (hb : d231381 q = 1) : d260700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d260700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65241 q ha hb
    | true =>
      simp only [d25544, d260700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25545 q = 1) (hb : d231381 q = 1) : d260701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d260701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25545, d260701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202056 q = 1) (hb : d231381 q = 1) : d260702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d260702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202056, d260702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202057 q = 1) (hb : d231381 q = 1) : d260703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d260703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202057, d260703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202058 q = 1) (hb : d231381 q = 1) : d260704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d260704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202058, d260704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202059 q = 1) (hb : d231381 q = 1) : d260705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d260705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202059, d260705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro65243 (p : Pattern) (ha : d202066 p = 1) (hb : d231381 p = 1) : d260714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25538 q = 1) (hb : d231381 q = 1) : d260697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d260697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65240 q ha hb
    | true =>
      simp only [d25538, d260697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65214 q ha hb
  have h2 (q : Pattern) (ha : d202055 q = 1) (hb : d231381 q = 1) : d260698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d260698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202055, d260698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25544 q = 1) (hb : d231381 q = 1) : d260700 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d260700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65241 q ha hb
    | true =>
      simp only [d25544, d260700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25545 q = 1) (hb : d231381 q = 1) : d260701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d260701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25545, d260701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d231381 q = 1) : d260702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d260702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202056, d260702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d231381 q = 1) : d260712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d260712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d260712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d231381 q = 1) : d260713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d260713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d260713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d231381 q = 1) : d260714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d260714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d260714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro65244 (p : Pattern) (ha : d25591 p = 1) (hb : d231381 p = 1) : d260729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d231381 q = 1) : d260720 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d260720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d260720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65227 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d231381 q = 1) : d260652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d260652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65227 q ha hb
    | true =>
      simp only [d25439, d260652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d231381 q = 1) : d260721 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d260721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d260721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d231381 q = 1) : d260653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d260653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d260653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d231381 q = 1) : d260722 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d260722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d260722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d231381 q = 1) : d260723 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d260723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d260723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d231381 q = 1) : d260724 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d260724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d260724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65228 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d231381 q = 1) : d260657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d260657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65228 q ha hb
    | true =>
      simp only [d25444, d260657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d231381 q = 1) : d260725 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d260725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d260725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d231381 q = 1) : d260658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d260658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d260658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d231381 q = 1) : d260726 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d260726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d260726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d231381 q = 1) : d260727 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d260727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d260727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d231381 q = 1) : d260728 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d260728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d260728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25586 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65229 q ha hb
  have h15 (q : Pattern) (ha : d25452 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65229 q ha hb
    | true =>
      simp only [d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25587 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25453 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25588 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25589 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d25314 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
  have h21 (q : Pattern) (ha : d25222 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
    | true =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25315 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d25223 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25316 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25317 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25590 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25591 q = 1) (hb : d231381 q = 1) : d260729 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25591, d260729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25591, d260729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro65245 (p : Pattern) (ha : d25595 p = 1) (hb : d231381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25314 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
  have h2 (q : Pattern) (ha : d25222 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65190 q ha hb
    | true =>
      simp only [d25222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25315 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25223 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25316 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25317 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56721 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25318 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25595 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro65246 (p : Pattern) (ha : d25601 p = 1) (hb : d231381 p = 1) : d260735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25592 q = 1) (hb : d231381 q = 1) : d260730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25592, d260730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65244 q ha hb
    | true =>
      simp only [d25592, d260730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65202 q ha hb
  have h2 (q : Pattern) (ha : d25593 q = 1) (hb : d231381 q = 1) : d260731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25593, d260731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25593, d260731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25594 q = 1) (hb : d231381 q = 1) : d260732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25594, d260732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25594, d260732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25596 q = 1) (hb : d231381 q = 1) : d235220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25596, d235220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65202 q ha hb
    | true =>
      simp only [d25596, d235220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65245 q ha hb
  have h5 (q : Pattern) (ha : d25597 q = 1) (hb : d231381 q = 1) : d235221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25597, d235221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25597, d235221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25598 q = 1) (hb : d231381 q = 1) : d235222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25598, d235222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25598, d235222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25599 q = 1) (hb : d231381 q = 1) : d260733 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25599, d260733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25599, d260733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25320 q = 1) (hb : d231381 q = 1) : d260594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d260594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65202 q ha hb
    | true =>
      simp only [d25320, d260594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
  have h9 (q : Pattern) (ha : d25321 q = 1) (hb : d231381 q = 1) : d260595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d260595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d260595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25322 q = 1) (hb : d231381 q = 1) : d260596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d260596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d260596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25154 q = 1) (hb : d231381 q = 1) : d234750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
    | true =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
  have h12 (q : Pattern) (ha : d25155 q = 1) (hb : d231381 q = 1) : d234751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25156 q = 1) (hb : d231381 q = 1) : d234752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25323 q = 1) (hb : d231381 q = 1) : d260597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d260597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25323, d260597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25600 q = 1) (hb : d231381 q = 1) : d260734 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25600, d260734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25600, d260734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25601 q = 1) (hb : d231381 q = 1) : d260735 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25601, d260735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25601, d260735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro65247 (p : Pattern) (ha : d25606 p = 1) (hb : d231381 p = 1) : d260599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d231381 q = 1) : d260594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d260594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65202 q ha hb
    | true =>
      simp only [d25320, d260594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d231381 q = 1) : d260595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d260595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d260595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d231381 q = 1) : d260596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d260596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d260596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25154 q = 1) (hb : d231381 q = 1) : d234750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65179 q ha hb
    | true =>
      simp only [d25154, d234750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56729 q ha hb
  have h5 (q : Pattern) (ha : d25155 q = 1) (hb : d231381 q = 1) : d234751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d234751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25156 q = 1) (hb : d231381 q = 1) : d234752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d234752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25323 q = 1) (hb : d231381 q = 1) : d260597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d260597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d260597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25604 q = 1) (hb : d231381 q = 1) : d234753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25604, d234753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25605 q = 1) (hb : d231381 q = 1) : d260598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25605, d260598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25605, d260598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25606 q = 1) (hb : d231381 q = 1) : d260599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25606, d260599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25606, d260599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro65248 (p : Pattern) (ha : d25612 p = 1) (hb : d231381 p = 1) : d260741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25602 q = 1) (hb : d231381 q = 1) : d260736 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25602, d260736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65246 q ha hb
    | true =>
      simp only [d25602, d260736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25603 q = 1) (hb : d231381 q = 1) : d260737 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25603, d260737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25603, d260737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25607 q = 1) (hb : d231381 q = 1) : d260600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d260600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65247 q ha hb
    | true =>
      simp only [d25607, d260600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25608 q = 1) (hb : d231381 q = 1) : d260601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d260601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d260601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25609 q = 1) (hb : d231381 q = 1) : d260738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25609, d260738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25609, d260738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25610 q = 1) (hb : d231381 q = 1) : d260739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25610, d260739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25610, d260739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25611 q = 1) (hb : d231381 q = 1) : d260740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25611, d260740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25611, d260740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25612 q = 1) (hb : d231381 q = 1) : d260741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25612, d260741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25612, d260741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro65249 (p : Pattern) (ha : d25620 p = 1) (hb : d231381 p = 1) : d260605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d231381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d231381 q = 1) : d260600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d260600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65247 q ha hb
    | true =>
      simp only [d25607, d260600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d231381 q = 1) : d260601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d260601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d260601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25615 q = 1) (hb : d231381 q = 1) : d234756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65220 q ha hb
    | true =>
      simp only [d25615, d234756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25616 q = 1) (hb : d231381 q = 1) : d234757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d234757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25617 q = 1) (hb : d231381 q = 1) : d260602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25617, d260602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25617, d260602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25618 q = 1) (hb : d231381 q = 1) : d260603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25618, d260603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25618, d260603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25619 q = 1) (hb : d231381 q = 1) : d260604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25619, d260604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25619, d260604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25620 q = 1) (hb : d231381 q = 1) : d260605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25620, d260605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25620, d260605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
