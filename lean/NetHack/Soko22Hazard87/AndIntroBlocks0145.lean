import NetHack.Soko22Hazard87.AndIntroBlocks0144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro36250 (p : Pattern) (ha : d14585 p = 1) (hb : d122306 p = 1) : d124321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d122306 q = 1) : d124318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d122306 q = 1) : d124319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d122306 q = 1) : d124320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14585 q = 1) (hb : d122306 q = 1) : d124321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14585, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14585, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36251 (p : Pattern) (ha : d122306 p = 1) (hb : d125534 p = 1) : d124327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d122306 q = 1) : d124290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36244 q ha hb
    | true =>
      simp only [d14515, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36245 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d122306 q = 1) : d124291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d122306 q = 1) : d124292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d122306 q = 1) : d124293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d122306 q = 1) : d124300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36246 q ha hb
    | true =>
      simp only [d14525, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36247 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d122306 q = 1) : d124301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d122306 q = 1) : d124302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d122306 q = 1) : d124316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36249 q ha hb
    | true =>
      simp only [d14549, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36232 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125530 q = 1) : d124317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125530, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d122306 q = 1) : d124322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36250 q ha hb
    | true =>
      simp only [d14586, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d122306 q = 1) : d124323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125531 q = 1) : d124324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125532 q = 1) : d124325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125532, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125533 q = 1) : d124326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125533, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125534 q = 1) : d124327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125534, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36252 (p : Pattern) (ha : d14592 p = 1) (hb : d122306 p = 1) : d124328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d122306 q = 1) : d124286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14592 q = 1) (hb : d122306 q = 1) : d124328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14592, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14592, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36253 (p : Pattern) (ha : d14593 p = 1) (hb : d122306 p = 1) : d124329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d122306 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14593 q = 1) (hb : d122306 q = 1) : d124329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14593, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14593, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36254 (p : Pattern) (ha : d14598 p = 1) (hb : d122306 p = 1) : d124334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d122306 q = 1) : d124294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d122306 q = 1) : d124295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14598 q = 1) (hb : d122306 q = 1) : d124334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14598, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14598, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36255 (p : Pattern) (ha : d14599 p = 1) (hb : d122306 p = 1) : d124335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d122306 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d122306 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14599 q = 1) (hb : d122306 q = 1) : d124335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14599, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14599, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36256 (p : Pattern) (ha : d14603 p = 1) (hb : d122306 p = 1) : d124339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d122306 q = 1) : d124310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36248 q ha hb
    | true =>
      simp only [d14543, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d122306 q = 1) : d124311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d122306 q = 1) : d124312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d122306 q = 1) : d124313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d122306 q = 1) : d124314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14603 q = 1) (hb : d122306 q = 1) : d124339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14603, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14603, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36257 (p : Pattern) (ha : d14609 p = 1) (hb : d122306 p = 1) : d124342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d122306 q = 1) : d124318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d122306 q = 1) : d124319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d122306 q = 1) : d124320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14609 q = 1) (hb : d122306 q = 1) : d124342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14609, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14609, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36258 (p : Pattern) (ha : d122306 p = 1) (hb : d125539 p = 1) : d124348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d122306 q = 1) : d124290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36244 q ha hb
    | true =>
      simp only [d14515, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36245 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d122306 q = 1) : d124291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d122306 q = 1) : d124292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d122306 q = 1) : d124293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d122306 q = 1) : d124300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36246 q ha hb
    | true =>
      simp only [d14525, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36247 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d122306 q = 1) : d124301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d122306 q = 1) : d124302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d122306 q = 1) : d124316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36249 q ha hb
    | true =>
      simp only [d14549, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36232 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125530 q = 1) : d124317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125530, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d122306 q = 1) : d124322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36250 q ha hb
    | true =>
      simp only [d14586, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d122306 q = 1) : d124323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125531 q = 1) : d124324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125532 q = 1) : d124325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125532, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125533 q = 1) : d124326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125533, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14594 q = 1) (hb : d122306 q = 1) : d124330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14594, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36252 q ha hb
    | true =>
      simp only [d14594, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36253 q ha hb
  have h16 (q : Pattern) (ha : d14595 q = 1) (hb : d122306 q = 1) : d124331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14595, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14595, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14596 q = 1) (hb : d122306 q = 1) : d124332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14596, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14596, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14597 q = 1) (hb : d122306 q = 1) : d124333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14597, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14597, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14600 q = 1) (hb : d122306 q = 1) : d124336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14600, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36254 q ha hb
    | true =>
      simp only [d14600, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36255 q ha hb
  have h20 (q : Pattern) (ha : d14601 q = 1) (hb : d122306 q = 1) : d124337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14601, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14601, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14602 q = 1) (hb : d122306 q = 1) : d124338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14602, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14602, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14604 q = 1) (hb : d122306 q = 1) : d124340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36256 q ha hb
    | true =>
      simp only [d14604, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36235 q ha hb
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125535 q = 1) : d124341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125535, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14610 q = 1) (hb : d122306 q = 1) : d124343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36257 q ha hb
    | true =>
      simp only [d14610, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14611 q = 1) (hb : d122306 q = 1) : d124344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14611, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122306 q = 1) (hb : d125536 q = 1) : d124345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125536, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122306 q = 1) (hb : d125537 q = 1) : d124346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125537, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122306 q = 1) (hb : d125538 q = 1) : d124347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125538, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122306 q = 1) (hb : d125539 q = 1) : d124348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125539, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36259 (p : Pattern) (ha : d122306 p = 1) (hb : d125546 p = 1) : d124368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14604 q = 1) (hb : d122306 q = 1) : d124340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36256 q ha hb
    | true =>
      simp only [d14604, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36235 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125535 q = 1) : d124341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125535, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14610 q = 1) (hb : d122306 q = 1) : d124343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36257 q ha hb
    | true =>
      simp only [d14610, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14611 q = 1) (hb : d122306 q = 1) : d124344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14611, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125536 q = 1) : d124345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125536, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125544 q = 1) : d124366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125544, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125545 q = 1) : d124367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125545, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125546 q = 1) : d124368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125546, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36260 (p : Pattern) (ha : d14667 p = 1) (hb : d122306 p = 1) : d124382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14650 q = 1) (hb : d122305 q = 1) : d124377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14650, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34581 q ha hb
    | true =>
      simp only [d14650, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
  have h2 (q : Pattern) (ha : d14651 q = 1) (hb : d122305 q = 1) : d124378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14651, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14651, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14652 q = 1) (hb : d122305 q = 1) : d124379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14652, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14652, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14657 q = 1) (hb : d122306 q = 1) : d124380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14657, d122306, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14657, d122306, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14659 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
  have h7 (q : Pattern) (ha : d14660 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14661 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14664 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14665 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14665, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14666 q = 1) (hb : d122306 q = 1) : d124381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14666, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14666, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14667 q = 1) (hb : d122306 q = 1) : d124382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14667, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14667, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36261 (p : Pattern) (ha : d14672 p = 1) (hb : d122306 p = 1) : d124390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14659 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14659, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
  have h2 (q : Pattern) (ha : d14660 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14661 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14664 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14665 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14665, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14662 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
    | true =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14663 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14664 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14670 q = 1) (hb : d122306 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14670, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14671 q = 1) (hb : d122306 q = 1) : d124389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14671, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14671, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14672 q = 1) (hb : d122306 q = 1) : d124390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14672, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14672, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36262 (p : Pattern) (ha : d14678 p = 1) (hb : d122306 p = 1) : d124396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14668 q = 1) (hb : d122306 q = 1) : d124383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14668, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36260 q ha hb
    | true =>
      simp only [d14668, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14669 q = 1) (hb : d122306 q = 1) : d124384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14669, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14669, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14673 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36261 q ha hb
    | true =>
      simp only [d14673, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14674 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14675 q = 1) (hb : d122306 q = 1) : d124393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14675, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14675, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14676 q = 1) (hb : d122306 q = 1) : d124394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14676, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14676, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14677 q = 1) (hb : d122306 q = 1) : d124395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14677, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14677, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14678 q = 1) (hb : d122306 q = 1) : d124396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14678, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14678, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36263 (p : Pattern) (ha : d14686 p = 1) (hb : d122306 p = 1) : d124404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36261 q ha hb
    | true =>
      simp only [d14673, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14681 q = 1) (hb : d122306 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36241 q ha hb
    | true =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14682 q = 1) (hb : d122306 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14683 q = 1) (hb : d122306 q = 1) : d124401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14683, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14683, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14684 q = 1) (hb : d122306 q = 1) : d124402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14684, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14684, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14685 q = 1) (hb : d122306 q = 1) : d124403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14685, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14685, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14686 q = 1) (hb : d122306 q = 1) : d124404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14686, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14686, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36264 (p : Pattern) (ha : d14725 p = 1) (hb : d122306 p = 1) : d124410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d122306 q = 1) : d124391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36261 q ha hb
    | true =>
      simp only [d14673, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d122306 q = 1) : d124392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14722 q = 1) (hb : d122306 q = 1) : d124407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14722, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14722, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14723 q = 1) (hb : d122306 q = 1) : d124408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14723, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14723, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14724 q = 1) (hb : d122306 q = 1) : d124409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14724, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14724, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14725 q = 1) (hb : d122306 q = 1) : d124410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14725, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14725, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36265 (p : Pattern) (ha : d122306 p = 1) (hb : d125556 p = 1) : d124416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14687 q = 1) (hb : d122306 q = 1) : d124405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14687, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36262 q ha hb
    | true =>
      simp only [d14687, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36263 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125552 q = 1) : d124406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125552, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14726 q = 1) (hb : d122306 q = 1) : d124411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14726, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36264 q ha hb
    | true =>
      simp only [d14726, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14727 q = 1) (hb : d122306 q = 1) : d124412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14727, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14727, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125553 q = 1) : d124413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125553, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125554 q = 1) : d124414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125554, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125555 q = 1) : d124415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125555, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125556 q = 1) : d124416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125556, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36266 (p : Pattern) (ha : d122306 p = 1) (hb : d125562 p = 1) : d124433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14498 q = 1) (hb : d122306 q = 1) : d124273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14498, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14498, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36234 q ha hb
  have h2 (q : Pattern) (ha : d14499 q = 1) (hb : d122306 q = 1) : d124274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14499, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14499, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14508 q = 1) (hb : d122306 q = 1) : d124283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36234 q ha hb
    | true =>
      simp only [d14508, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36237 q ha hb
  have h4 (q : Pattern) (ha : d14509 q = 1) (hb : d122306 q = 1) : d124284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14509, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14510 q = 1) (hb : d122306 q = 1) : d124285 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14510, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14510, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125540 q = 1) : d124349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36251 q ha hb
    | true =>
      simp only [d125540, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36258 q ha hb
  have h7 (q : Pattern) (ha : d14629 q = 1) (hb : d122306 q = 1) : d124362 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14629, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36238 q ha hb
    | true =>
      simp only [d14629, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36239 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125541 q = 1) : d124363 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125541, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125542 q = 1) : d124364 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125542, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125543 q = 1) : d124365 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125543, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125547 q = 1) : d124369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125547, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36259 q ha hb
  have h12 (q : Pattern) (ha : d14638 q = 1) (hb : d122306 q = 1) : d124371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14638, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14638, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36240 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125548 q = 1) : d124372 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125548, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125549 q = 1) : d124373 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125549, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125550 q = 1) : d124374 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125550, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125551 q = 1) : d124375 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125551, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125557 q = 1) : d124417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125557, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36265 q ha hb
  have h18 (q : Pattern) (ha : d14743 q = 1) (hb : d122306 q = 1) : d124428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14743, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14743, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36243 q ha hb
  have h19 (q : Pattern) (ha : d122306 q = 1) (hb : d125558 q = 1) : d124429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125558, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122306 q = 1) (hb : d125559 q = 1) : d124430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125559, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122306 q = 1) (hb : d125560 q = 1) : d124431 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125560, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122306 q = 1) (hb : d125561 q = 1) : d124432 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125561, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125562 q = 1) : d124433 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125562, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36267 (p : Pattern) (ha : d122306 p = 1) (hb : d125568 p = 1) : d124439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125563 q = 1) : d124434 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125563, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36266 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125564 q = 1) : d124435 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125564, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125565 q = 1) : d124436 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125565, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125566 q = 1) : d124437 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125566, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125567 q = 1) : d124438 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125567, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125568 q = 1) : d124439 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125568, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36268 (p : Pattern) (ha : d14784 p = 1) (hb : d122306 p = 1) : d124453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14777 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14779 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34594 q ha hb
  have h7 (q : Pattern) (ha : d14780 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14781 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14782 q = 1) (hb : d122306 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14782, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14783 q = 1) (hb : d122306 q = 1) : d124452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14783, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14783, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14784 q = 1) (hb : d122306 q = 1) : d124453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14784, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14784, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36269 (p : Pattern) (ha : d14788 p = 1) (hb : d122306 p = 1) : d124457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14779 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14779, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34594 q ha hb
  have h2 (q : Pattern) (ha : d14780 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14781 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14782 q = 1) (hb : d122306 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14782, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14787 q = 1) (hb : d122306 q = 1) : d124456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14787, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14787, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14788 q = 1) (hb : d122306 q = 1) : d124457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14788, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14788, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro36270 (p : Pattern) (ha : d14794 p = 1) (hb : d122306 p = 1) : d124463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36268 q ha hb
    | true =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d122306 q = 1) : d124462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14794 q = 1) (hb : d122306 q = 1) : d124463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14794, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14794, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36271 (p : Pattern) (ha : d14798 p = 1) (hb : d122306 p = 1) : d124467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d122306 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14798 q = 1) (hb : d122306 q = 1) : d124467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14798, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14798, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36272 (p : Pattern) (ha : d14804 p = 1) (hb : d122306 p = 1) : d124473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d122306 q = 1) : d124468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36270 q ha hb
    | true =>
      simp only [d14799, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36271 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d122306 q = 1) : d124469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d122306 q = 1) : d124470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d122306 q = 1) : d124471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d122306 q = 1) : d124472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14804 q = 1) (hb : d122306 q = 1) : d124473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36273 (p : Pattern) (ha : d14807 p = 1) (hb : d122306 p = 1) : d124476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36268 q ha hb
    | true =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d122306 q = 1) : d124462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14807 q = 1) (hb : d122306 q = 1) : d124476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14807, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14807, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36274 (p : Pattern) (ha : d14808 p = 1) (hb : d122306 p = 1) : d124477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d122306 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14808 q = 1) (hb : d122306 q = 1) : d124477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14808, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14808, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36275 (p : Pattern) (ha : d14814 p = 1) (hb : d122306 p = 1) : d124483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d122306 q = 1) : d124468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36270 q ha hb
    | true =>
      simp only [d14799, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36271 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d122306 q = 1) : d124469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d122306 q = 1) : d124470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d122306 q = 1) : d124471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d122306 q = 1) : d124472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14809 q = 1) (hb : d122306 q = 1) : d124478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36273 q ha hb
    | true =>
      simp only [d14809, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36274 q ha hb
  have h7 (q : Pattern) (ha : d14810 q = 1) (hb : d122306 q = 1) : d124479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14811 q = 1) (hb : d122306 q = 1) : d124480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14811, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14812 q = 1) (hb : d122306 q = 1) : d124481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14813 q = 1) (hb : d122306 q = 1) : d124482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14814 q = 1) (hb : d122306 q = 1) : d124483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14814, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36276 (p : Pattern) (ha : d14855 p = 1) (hb : d122306 p = 1) : d124518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14777 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14774 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14774, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34593 q ha hb
  have h7 (q : Pattern) (ha : d14775 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14776 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14853 q = 1) (hb : d122306 q = 1) : d124516 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14853, d122306, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14853, d122306, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14854 q = 1) (hb : d122306 q = 1) : d124517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14854, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14854, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14855 q = 1) (hb : d122306 q = 1) : d124518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14855, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14855, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36277 (p : Pattern) (ha : d14865 p = 1) (hb : d122306 p = 1) : d124528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36276 q ha hb
    | true =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d122306 q = 1) : d124525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d122306 q = 1) : d124526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d122306 q = 1) : d124527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14865 q = 1) (hb : d122306 q = 1) : d124528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14865, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14865, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36278 (p : Pattern) (ha : d14965 p = 1) (hb : d122306 p = 1) : d124574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14955 q = 1) (hb : d122306 q = 1) : d124564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14955, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36277 q ha hb
    | true =>
      simp only [d14955, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36271 q ha hb
  have h2 (q : Pattern) (ha : d14956 q = 1) (hb : d122306 q = 1) : d124565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14956, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14956, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14957 q = 1) (hb : d122306 q = 1) : d124566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14957, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14957, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14958 q = 1) (hb : d122306 q = 1) : d124567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14958, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14958, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14959 q = 1) (hb : d122306 q = 1) : d124568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14959, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14959, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14960 q = 1) (hb : d122306 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36271 q ha hb
    | true =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14961 q = 1) (hb : d122306 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14962 q = 1) (hb : d122306 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14963 q = 1) (hb : d122306 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14964 q = 1) (hb : d122306 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14965 q = 1) (hb : d122306 q = 1) : d124574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14965, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14965, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36279 (p : Pattern) (ha : d14971 p = 1) (hb : d122306 p = 1) : d124580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14960 q = 1) (hb : d122306 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36271 q ha hb
    | true =>
      simp only [d14960, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14961 q = 1) (hb : d122306 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14962 q = 1) (hb : d122306 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14962, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14963 q = 1) (hb : d122306 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14964 q = 1) (hb : d122306 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14966 q = 1) (hb : d122306 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36274 q ha hb
    | true =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14967 q = 1) (hb : d122306 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14968 q = 1) (hb : d122306 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14969 q = 1) (hb : d122306 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14970 q = 1) (hb : d122306 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14971 q = 1) (hb : d122306 q = 1) : d124580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14971, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14971, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36280 (p : Pattern) (ha : d14980 p = 1) (hb : d122306 p = 1) : d124589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14966 q = 1) (hb : d122306 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36274 q ha hb
    | true =>
      simp only [d14966, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14967 q = 1) (hb : d122306 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14968 q = 1) (hb : d122306 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14968, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14969 q = 1) (hb : d122306 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14970 q = 1) (hb : d122306 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14980 q = 1) (hb : d122306 q = 1) : d124589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14980, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14980, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36281 (p : Pattern) (ha : d15048 p = 1) (hb : d122306 p = 1) : d124627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15043 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15043, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34609 q ha hb
  have h2 (q : Pattern) (ha : d15044 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15045 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15046 q = 1) (hb : d122306 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15046, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15047 q = 1) (hb : d122306 q = 1) : d124626 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15047, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15047, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15048 q = 1) (hb : d122306 q = 1) : d124627 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15048, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15048, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro36282 (p : Pattern) (ha : d15128 p = 1) (hb : d122306 p = 1) : d124654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15049 q = 1) (hb : d122306 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36281 q ha hb
    | true =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15050 q = 1) (hb : d122306 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15125 q = 1) (hb : d122306 q = 1) : d124651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15125, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15125, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15126 q = 1) (hb : d122306 q = 1) : d124652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15126, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15126, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15127 q = 1) (hb : d122306 q = 1) : d124653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15127, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15127, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15128 q = 1) (hb : d122306 q = 1) : d124654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15128, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15128, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36283 (p : Pattern) (ha : d15134 p = 1) (hb : d122306 p = 1) : d124660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15129 q = 1) (hb : d122306 q = 1) : d124655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15129, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36282 q ha hb
    | true =>
      simp only [d15129, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15130 q = 1) (hb : d122306 q = 1) : d124656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15130, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15130, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15131 q = 1) (hb : d122306 q = 1) : d124657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15131, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15131, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15132 q = 1) (hb : d122306 q = 1) : d124658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15132, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15132, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15133 q = 1) (hb : d122306 q = 1) : d124659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15133, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15133, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15134 q = 1) (hb : d122306 q = 1) : d124660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15134, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15134, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36284 (p : Pattern) (ha : d14819 p = 1) (hb : d122306 p = 1) : d124488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36268 q ha hb
    | true =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d122306 q = 1) : d124487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14819 q = 1) (hb : d122306 q = 1) : d124488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14819, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14819, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36285 (p : Pattern) (ha : d14821 p = 1) (hb : d122306 p = 1) : d124490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d122306 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14821 q = 1) (hb : d122306 q = 1) : d124490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14821, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14821, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36286 (p : Pattern) (ha : d14828 p = 1) (hb : d122306 p = 1) : d124497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36268 q ha hb
    | true =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d122306 q = 1) : d124495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d122306 q = 1) : d124496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14828 q = 1) (hb : d122306 q = 1) : d124497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14828, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14828, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36287 (p : Pattern) (ha : d14831 p = 1) (hb : d122306 p = 1) : d124500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d122306 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d122306 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14831 q = 1) (hb : d122306 q = 1) : d124500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14831, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14831, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36288 (p : Pattern) (ha : d14850 p = 1) (hb : d122306 p = 1) : d124510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14840 q = 1) (hb : d122305 q = 1) : d124505 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14840, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34617 q ha hb
    | true =>
      simp only [d14840, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
  have h2 (q : Pattern) (ha : d14841 q = 1) (hb : d122305 q = 1) : d124506 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14841, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14841, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14842 q = 1) (hb : d122305 q = 1) : d124507 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14842, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14842, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14847 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14848 q = 1) (hb : d122306 q = 1) : d124508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14848, d122306, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14848, d122306, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h7 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14776 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14777 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14849 q = 1) (hb : d122306 q = 1) : d124509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14849, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14849, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14850 q = 1) (hb : d122306 q = 1) : d124510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14850, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14850, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36289 (p : Pattern) (ha : d14861 p = 1) (hb : d122306 p = 1) : d124524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d122306 q = 1) : d124511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36288 q ha hb
    | true =>
      simp only [d14851, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d122306 q = 1) : d124512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36276 q ha hb
    | true =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d122306 q = 1) : d124521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d122306 q = 1) : d124522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d122306 q = 1) : d124523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14861 q = 1) (hb : d122306 q = 1) : d124524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14861, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14861, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36290 (p : Pattern) (ha : d14916 p = 1) (hb : d122306 p = 1) : d124453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14767 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34591 q ha hb
    | true =>
      simp only [d14767, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
  have h2 (q : Pattern) (ha : d14768 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14769 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14777 q = 1) (hb : d122306 q = 1) : d124447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14777, d122306, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12961 q = 1) (hb : d122305 q = 1) : d12961 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14911 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14911, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34592 q ha hb
    | true =>
      simp only [d14911, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14912 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14912, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14912, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14913 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14913, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14913, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14914 q = 1) (hb : d122306 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14914, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14914, d122306, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14915 q = 1) (hb : d122306 q = 1) : d124452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14915, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14915, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14916 q = 1) (hb : d122306 q = 1) : d124453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14916, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14916, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36291 (p : Pattern) (ha : d14922 p = 1) (hb : d122306 p = 1) : d124534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36290 q ha hb
    | true =>
      simp only [d14917, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d122306 q = 1) : d124531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d122306 q = 1) : d124532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d122306 q = 1) : d124533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14922 q = 1) (hb : d122306 q = 1) : d124534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14922, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14922, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36292 (p : Pattern) (ha : d122306 p = 1) (hb : d125575 p = 1) : d124540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d122306 q = 1) : d124491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36284 q ha hb
    | true =>
      simp only [d14822, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36285 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d122306 q = 1) : d124492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d122306 q = 1) : d124493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d122306 q = 1) : d124494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d122306 q = 1) : d124501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36286 q ha hb
    | true =>
      simp only [d14832, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36287 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d122306 q = 1) : d124502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d122306 q = 1) : d124503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d122306 q = 1) : d124529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36289 q ha hb
    | true =>
      simp only [d14866, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36277 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125571 q = 1) : d124530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125571, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d122306 q = 1) : d124535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36291 q ha hb
    | true =>
      simp only [d14923, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d122306 q = 1) : d124536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125572 q = 1) : d124537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125573 q = 1) : d124538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125573, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125574 q = 1) : d124539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125574, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125575 q = 1) : d124540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125575, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36293 (p : Pattern) (ha : d14929 p = 1) (hb : d122306 p = 1) : d124541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36268 q ha hb
    | true =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d122306 q = 1) : d124461 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d122306 q = 1) : d124487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14929 q = 1) (hb : d122306 q = 1) : d124541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14929, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14929, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36294 (p : Pattern) (ha : d14930 p = 1) (hb : d122306 p = 1) : d124542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d122306 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d122306 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14930 q = 1) (hb : d122306 q = 1) : d124542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14930, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14930, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36295 (p : Pattern) (ha : d14935 p = 1) (hb : d122306 p = 1) : d124547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36268 q ha hb
    | true =>
      simp only [d14785, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d122306 q = 1) : d124460 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d122306 q = 1) : d124495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d122306 q = 1) : d124496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14935 q = 1) (hb : d122306 q = 1) : d124547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14935, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14935, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36296 (p : Pattern) (ha : d14936 p = 1) (hb : d122306 p = 1) : d124548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d122306 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d122306 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d122306 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14936 q = 1) (hb : d122306 q = 1) : d124548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14936, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14936, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36297 (p : Pattern) (ha : d14940 p = 1) (hb : d122306 p = 1) : d124552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d122306 q = 1) : d124511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36288 q ha hb
    | true =>
      simp only [d14851, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d122306 q = 1) : d124512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36276 q ha hb
    | true =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d122306 q = 1) : d124521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d122306 q = 1) : d124522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d122306 q = 1) : d124523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14940 q = 1) (hb : d122306 q = 1) : d124552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14940, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14940, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36298 (p : Pattern) (ha : d14941 p = 1) (hb : d122306 p = 1) : d124553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d122306 q = 1) : d124519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36276 q ha hb
    | true =>
      simp only [d14856, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d122306 q = 1) : d124520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d122306 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36269 q ha hb
    | true =>
      simp only [d14789, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d122306 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d122306 q = 1) : d124525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d122306 q = 1) : d124526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d122306 q = 1) : d124527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14941 q = 1) (hb : d122306 q = 1) : d124553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14941, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14941, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36299 (p : Pattern) (ha : d14947 p = 1) (hb : d122306 p = 1) : d124556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d122306 q = 1) : d124454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36290 q ha hb
    | true =>
      simp only [d14917, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d122306 q = 1) : d124455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d122306 q = 1) : d124531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d122306 q = 1) : d124532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d122306 q = 1) : d124533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14947 q = 1) (hb : d122306 q = 1) : d124556 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14947, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14947, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36300 (p : Pattern) (ha : d122306 p = 1) (hb : d125580 p = 1) : d124562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d122306 q = 1) : d124491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36284 q ha hb
    | true =>
      simp only [d14822, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36285 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d122306 q = 1) : d124492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d122306 q = 1) : d124493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d122306 q = 1) : d124494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d122306 q = 1) : d124501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36286 q ha hb
    | true =>
      simp only [d14832, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36287 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d122306 q = 1) : d124502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d122306 q = 1) : d124503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d122306 q = 1) : d124529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36289 q ha hb
    | true =>
      simp only [d14866, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36277 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125571 q = 1) : d124530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125571, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d122306 q = 1) : d124535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36291 q ha hb
    | true =>
      simp only [d14923, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d122306 q = 1) : d124536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125572 q = 1) : d124537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125573 q = 1) : d124538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125573, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125574 q = 1) : d124539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125574, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14931 q = 1) (hb : d122306 q = 1) : d124543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14931, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36293 q ha hb
    | true =>
      simp only [d14931, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36294 q ha hb
  have h16 (q : Pattern) (ha : d14932 q = 1) (hb : d122306 q = 1) : d124544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14932, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14932, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14933 q = 1) (hb : d122306 q = 1) : d124545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14933, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14933, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14934 q = 1) (hb : d122306 q = 1) : d124546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14934, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14934, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14937 q = 1) (hb : d122306 q = 1) : d124549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14937, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36295 q ha hb
    | true =>
      simp only [d14937, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36296 q ha hb
  have h20 (q : Pattern) (ha : d14938 q = 1) (hb : d122306 q = 1) : d124550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14938, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14938, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14939 q = 1) (hb : d122306 q = 1) : d124551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14939, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14939, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14942 q = 1) (hb : d122306 q = 1) : d124554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36297 q ha hb
    | true =>
      simp only [d14942, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36298 q ha hb
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125576 q = 1) : d124555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125576, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14948 q = 1) (hb : d122306 q = 1) : d124557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36299 q ha hb
    | true =>
      simp only [d14948, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14949 q = 1) (hb : d122306 q = 1) : d124558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14949, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122306 q = 1) (hb : d125577 q = 1) : d124559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125577, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122306 q = 1) (hb : d125578 q = 1) : d124560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125578, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122306 q = 1) (hb : d125579 q = 1) : d124561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125579, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122306 q = 1) (hb : d125580 q = 1) : d124562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125580, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36301 (p : Pattern) (ha : d122306 p = 1) (hb : d125587 p = 1) : d124587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14942 q = 1) (hb : d122306 q = 1) : d124554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36297 q ha hb
    | true =>
      simp only [d14942, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36298 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125576 q = 1) : d124555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125576, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14948 q = 1) (hb : d122306 q = 1) : d124557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36299 q ha hb
    | true =>
      simp only [d14948, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14949 q = 1) (hb : d122306 q = 1) : d124558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14949, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125577 q = 1) : d124559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125577, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125585 q = 1) : d124585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125585, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125586 q = 1) : d124586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125586, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125587 q = 1) : d124587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125587, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36302 (p : Pattern) (ha : d15030 p = 1) (hb : d122306 p = 1) : d124607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15000 q = 1) (hb : d122305 q = 1) : d124597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15000, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34633 q ha hb
    | true =>
      simp only [d15000, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
  have h2 (q : Pattern) (ha : d15001 q = 1) (hb : d122305 q = 1) : d124598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15001, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15001, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15002 q = 1) (hb : d122305 q = 1) : d124599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15002, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15002, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15012 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15013 q = 1) (hb : d122306 q = 1) : d124600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15013, d122306, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15013, d122306, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h7 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15027 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15028 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15029 q = 1) (hb : d122306 q = 1) : d124606 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15029, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15029, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15030 q = 1) (hb : d122306 q = 1) : d124607 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15030, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15030, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36303 (p : Pattern) (ha : d15035 p = 1) (hb : d122306 p = 1) : d124615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15027 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15028 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15025 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15025, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34636 q ha hb
  have h7 (q : Pattern) (ha : d15026 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15027 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15033 q = 1) (hb : d122306 q = 1) : d124613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15033, d122306, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15033, d122306, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15034 q = 1) (hb : d122306 q = 1) : d124614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15034, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15034, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15035 q = 1) (hb : d122306 q = 1) : d124615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15035, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15035, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36304 (p : Pattern) (ha : d15041 p = 1) (hb : d122306 p = 1) : d124621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15031 q = 1) (hb : d122306 q = 1) : d124608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15031, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36302 q ha hb
    | true =>
      simp only [d15031, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15032 q = 1) (hb : d122306 q = 1) : d124609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15032, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15032, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15036 q = 1) (hb : d122306 q = 1) : d124616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36303 q ha hb
    | true =>
      simp only [d15036, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15037 q = 1) (hb : d122306 q = 1) : d124617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15038 q = 1) (hb : d122306 q = 1) : d124618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15038, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15038, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15039 q = 1) (hb : d122306 q = 1) : d124619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15039, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15039, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15040 q = 1) (hb : d122306 q = 1) : d124620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15040, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15040, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15041 q = 1) (hb : d122306 q = 1) : d124621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15041, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15041, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36305 (p : Pattern) (ha : d15054 p = 1) (hb : d122306 p = 1) : d124633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15036 q = 1) (hb : d122306 q = 1) : d124616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36303 q ha hb
    | true =>
      simp only [d15036, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15037 q = 1) (hb : d122306 q = 1) : d124617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d122306 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36281 q ha hb
    | true =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d122306 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15051 q = 1) (hb : d122306 q = 1) : d124630 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15051, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15051, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15052 q = 1) (hb : d122306 q = 1) : d124631 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15052, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15052, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15053 q = 1) (hb : d122306 q = 1) : d124632 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15053, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15053, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15054 q = 1) (hb : d122306 q = 1) : d124633 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15054, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15054, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36306 (p : Pattern) (ha : d15111 p = 1) (hb : d122306 p = 1) : d124637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15027 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15028 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13190 q = 1) (hb : d122305 q = 1) : d13190 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15106 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15106, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15106, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15107 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15107, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15107, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15108 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15108, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15108, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15109 q = 1) (hb : d122306 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15109, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15109, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15110 q = 1) (hb : d122306 q = 1) : d124636 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15110, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15110, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15111 q = 1) (hb : d122306 q = 1) : d124637 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15111, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15111, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36307 (p : Pattern) (ha : d15117 p = 1) (hb : d122306 p = 1) : d124643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15112 q = 1) (hb : d122306 q = 1) : d124638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15112, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36306 q ha hb
    | true =>
      simp only [d15112, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15113 q = 1) (hb : d122306 q = 1) : d124639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15113, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15113, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15114 q = 1) (hb : d122306 q = 1) : d124640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15114, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15114, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15115 q = 1) (hb : d122306 q = 1) : d124641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15115, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15115, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15116 q = 1) (hb : d122306 q = 1) : d124642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15116, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15116, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15117 q = 1) (hb : d122306 q = 1) : d124643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15117, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15117, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36308 (p : Pattern) (ha : d122306 p = 1) (hb : d125597 p = 1) : d124649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15055 q = 1) (hb : d122306 q = 1) : d124634 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15055, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36304 q ha hb
    | true =>
      simp only [d15055, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36305 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125593 q = 1) : d124635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125593, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15118 q = 1) (hb : d122306 q = 1) : d124644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15118, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36307 q ha hb
    | true =>
      simp only [d15118, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15119 q = 1) (hb : d122306 q = 1) : d124645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15119, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15119, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125594 q = 1) : d124646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125594, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125595 q = 1) : d124647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125595, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125596 q = 1) : d124648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125596, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125597 q = 1) : d124649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125597, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36309 (p : Pattern) (ha : d122306 p = 1) (hb : d125603 p = 1) : d124666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14805 q = 1) (hb : d122306 q = 1) : d124474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14805, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14805, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36272 q ha hb
  have h2 (q : Pattern) (ha : d14806 q = 1) (hb : d122306 q = 1) : d124475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14806, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14806, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14815 q = 1) (hb : d122306 q = 1) : d124484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36272 q ha hb
    | true =>
      simp only [d14815, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36275 q ha hb
  have h4 (q : Pattern) (ha : d14816 q = 1) (hb : d122306 q = 1) : d124485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14816, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14817 q = 1) (hb : d122306 q = 1) : d124486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14817, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14817, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125581 q = 1) : d124563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36292 q ha hb
    | true =>
      simp only [d125581, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36300 q ha hb
  have h7 (q : Pattern) (ha : d14972 q = 1) (hb : d122306 q = 1) : d124581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14972, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36278 q ha hb
    | true =>
      simp only [d14972, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36279 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125582 q = 1) : d124582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125582, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125583 q = 1) : d124583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125583, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125584 q = 1) : d124584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125584, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125588 q = 1) : d124588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125588, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36301 q ha hb
  have h12 (q : Pattern) (ha : d14981 q = 1) (hb : d122306 q = 1) : d124590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14981, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14981, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36280 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125589 q = 1) : d124591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125589, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125590 q = 1) : d124592 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125590, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125591 q = 1) : d124593 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125591, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125592 q = 1) : d124594 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125592, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125598 q = 1) : d124650 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125598, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36308 q ha hb
  have h18 (q : Pattern) (ha : d15135 q = 1) (hb : d122306 q = 1) : d124661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15135, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15135, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36283 q ha hb
  have h19 (q : Pattern) (ha : d122306 q = 1) (hb : d125599 q = 1) : d124662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125599, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122306 q = 1) (hb : d125600 q = 1) : d124663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125600, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122306 q = 1) (hb : d125601 q = 1) : d124664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125601, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122306 q = 1) (hb : d125602 q = 1) : d124665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125602, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125603 q = 1) : d124666 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125603, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36310 (p : Pattern) (ha : d122306 p = 1) (hb : d125609 p = 1) : d124672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125604 q = 1) : d124667 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125604, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36309 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125605 q = 1) : d124668 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125605, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125606 q = 1) : d124669 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125606, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125607 q = 1) : d124670 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125607, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125608 q = 1) : d124671 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125608, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125609 q = 1) : d124672 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125609, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36311 (p : Pattern) (ha : d15177 p = 1) (hb : d122306 p = 1) : d124687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15170 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15172 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34649 q ha hb
  have h7 (q : Pattern) (ha : d15173 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15174 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15175 q = 1) (hb : d122306 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15175, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15176 q = 1) (hb : d122306 q = 1) : d124686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15176, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15176, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15177 q = 1) (hb : d122306 q = 1) : d124687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15177, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15177, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36312 (p : Pattern) (ha : d15181 p = 1) (hb : d122306 p = 1) : d124691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15172 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15172, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34649 q ha hb
  have h2 (q : Pattern) (ha : d15173 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15174 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15175 q = 1) (hb : d122306 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15175, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15180 q = 1) (hb : d122306 q = 1) : d124690 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15180, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15180, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15181 q = 1) (hb : d122306 q = 1) : d124691 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15181, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15181, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro36313 (p : Pattern) (ha : d15187 p = 1) (hb : d122306 p = 1) : d124697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36311 q ha hb
    | true =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d122306 q = 1) : d124696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15187 q = 1) (hb : d122306 q = 1) : d124697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15187, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15187, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36314 (p : Pattern) (ha : d15191 p = 1) (hb : d122306 p = 1) : d124701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d122306 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15191 q = 1) (hb : d122306 q = 1) : d124701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15191, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15191, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36315 (p : Pattern) (ha : d15197 p = 1) (hb : d122306 p = 1) : d124707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d122306 q = 1) : d124702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36313 q ha hb
    | true =>
      simp only [d15192, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36314 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d122306 q = 1) : d124703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d122306 q = 1) : d124704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d122306 q = 1) : d124705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d122306 q = 1) : d124706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15197 q = 1) (hb : d122306 q = 1) : d124707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36316 (p : Pattern) (ha : d15200 p = 1) (hb : d122306 p = 1) : d124710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36311 q ha hb
    | true =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d122306 q = 1) : d124696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15200 q = 1) (hb : d122306 q = 1) : d124710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15200, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15200, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36317 (p : Pattern) (ha : d15201 p = 1) (hb : d122306 p = 1) : d124711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d122306 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15201 q = 1) (hb : d122306 q = 1) : d124711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15201, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15201, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36318 (p : Pattern) (ha : d15207 p = 1) (hb : d122306 p = 1) : d124717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d122306 q = 1) : d124702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36313 q ha hb
    | true =>
      simp only [d15192, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36314 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d122306 q = 1) : d124703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d122306 q = 1) : d124704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d122306 q = 1) : d124705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d122306 q = 1) : d124706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15202 q = 1) (hb : d122306 q = 1) : d124712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36316 q ha hb
    | true =>
      simp only [d15202, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36317 q ha hb
  have h7 (q : Pattern) (ha : d15203 q = 1) (hb : d122306 q = 1) : d124713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15204 q = 1) (hb : d122306 q = 1) : d124714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15204, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15205 q = 1) (hb : d122306 q = 1) : d124715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15206 q = 1) (hb : d122306 q = 1) : d124716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15207 q = 1) (hb : d122306 q = 1) : d124717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15207, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36319 (p : Pattern) (ha : d15248 p = 1) (hb : d122306 p = 1) : d124752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15170 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15167 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15167, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34648 q ha hb
  have h7 (q : Pattern) (ha : d15168 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15169 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15246 q = 1) (hb : d122306 q = 1) : d124750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, d122306, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15246, d122306, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15247 q = 1) (hb : d122306 q = 1) : d124751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15247, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15248 q = 1) (hb : d122306 q = 1) : d124752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15248, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36320 (p : Pattern) (ha : d15258 p = 1) (hb : d122306 p = 1) : d124762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36319 q ha hb
    | true =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d122306 q = 1) : d124759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d122306 q = 1) : d124760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d122306 q = 1) : d124761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15258 q = 1) (hb : d122306 q = 1) : d124762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15258, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36321 (p : Pattern) (ha : d15358 p = 1) (hb : d122306 p = 1) : d124808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15348 q = 1) (hb : d122306 q = 1) : d124798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36320 q ha hb
    | true =>
      simp only [d15348, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36314 q ha hb
  have h2 (q : Pattern) (ha : d15349 q = 1) (hb : d122306 q = 1) : d124799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15349, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15350 q = 1) (hb : d122306 q = 1) : d124800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15350, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15351 q = 1) (hb : d122306 q = 1) : d124801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15351, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15352 q = 1) (hb : d122306 q = 1) : d124802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15352, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15353 q = 1) (hb : d122306 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36314 q ha hb
    | true =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15354 q = 1) (hb : d122306 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15355 q = 1) (hb : d122306 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15356 q = 1) (hb : d122306 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15357 q = 1) (hb : d122306 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15358 q = 1) (hb : d122306 q = 1) : d124808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15358, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36322 (p : Pattern) (ha : d15364 p = 1) (hb : d122306 p = 1) : d124814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15353 q = 1) (hb : d122306 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36314 q ha hb
    | true =>
      simp only [d15353, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15354 q = 1) (hb : d122306 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15355 q = 1) (hb : d122306 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15355, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15356 q = 1) (hb : d122306 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15357 q = 1) (hb : d122306 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15359 q = 1) (hb : d122306 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36317 q ha hb
    | true =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15360 q = 1) (hb : d122306 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15361 q = 1) (hb : d122306 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15362 q = 1) (hb : d122306 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15363 q = 1) (hb : d122306 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15364 q = 1) (hb : d122306 q = 1) : d124814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15364, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36323 (p : Pattern) (ha : d15373 p = 1) (hb : d122306 p = 1) : d124823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15359 q = 1) (hb : d122306 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36317 q ha hb
    | true =>
      simp only [d15359, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15360 q = 1) (hb : d122306 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15361 q = 1) (hb : d122306 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15361, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15362 q = 1) (hb : d122306 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15363 q = 1) (hb : d122306 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15373 q = 1) (hb : d122306 q = 1) : d124823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15373, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36324 (p : Pattern) (ha : d15441 p = 1) (hb : d122306 p = 1) : d124861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15436 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15436, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34664 q ha hb
  have h2 (q : Pattern) (ha : d15437 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15438 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15439 q = 1) (hb : d122306 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15439, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15440 q = 1) (hb : d122306 q = 1) : d124860 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15440, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15441 q = 1) (hb : d122306 q = 1) : d124861 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15441, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro36325 (p : Pattern) (ha : d15521 p = 1) (hb : d122306 p = 1) : d124888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15442 q = 1) (hb : d122306 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36324 q ha hb
    | true =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15443 q = 1) (hb : d122306 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15518 q = 1) (hb : d122306 q = 1) : d124885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15518, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15519 q = 1) (hb : d122306 q = 1) : d124886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15519, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15520 q = 1) (hb : d122306 q = 1) : d124887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15520, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15521 q = 1) (hb : d122306 q = 1) : d124888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15521, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36326 (p : Pattern) (ha : d15527 p = 1) (hb : d122306 p = 1) : d124894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15522 q = 1) (hb : d122306 q = 1) : d124889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36325 q ha hb
    | true =>
      simp only [d15522, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15523 q = 1) (hb : d122306 q = 1) : d124890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15523, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15524 q = 1) (hb : d122306 q = 1) : d124891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15524, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15525 q = 1) (hb : d122306 q = 1) : d124892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15525, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15526 q = 1) (hb : d122306 q = 1) : d124893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15526, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15527 q = 1) (hb : d122306 q = 1) : d124894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15527, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36327 (p : Pattern) (ha : d15212 p = 1) (hb : d122306 p = 1) : d124722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36311 q ha hb
    | true =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d122306 q = 1) : d124721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15212 q = 1) (hb : d122306 q = 1) : d124722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15212, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15212, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36328 (p : Pattern) (ha : d15214 p = 1) (hb : d122306 p = 1) : d124724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d122306 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15214 q = 1) (hb : d122306 q = 1) : d124724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15214, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15214, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36329 (p : Pattern) (ha : d15221 p = 1) (hb : d122306 p = 1) : d124731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36311 q ha hb
    | true =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d122306 q = 1) : d124729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d122306 q = 1) : d124730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15221 q = 1) (hb : d122306 q = 1) : d124731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15221, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15221, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36330 (p : Pattern) (ha : d15224 p = 1) (hb : d122306 p = 1) : d124734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d122306 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d122306 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15224 q = 1) (hb : d122306 q = 1) : d124734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15224, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15224, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36331 (p : Pattern) (ha : d15243 p = 1) (hb : d122306 p = 1) : d124744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15233 q = 1) (hb : d122305 q = 1) : d124739 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15233, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34672 q ha hb
    | true =>
      simp only [d15233, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
  have h2 (q : Pattern) (ha : d15234 q = 1) (hb : d122305 q = 1) : d124740 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15234, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15234, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15235 q = 1) (hb : d122305 q = 1) : d124741 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15235, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15235, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15240 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15241 q = 1) (hb : d122306 q = 1) : d124742 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15241, d122306, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15241, d122306, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h7 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15169 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15170 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15242 q = 1) (hb : d122306 q = 1) : d124743 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15242, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15242, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15243 q = 1) (hb : d122306 q = 1) : d124744 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15243, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15243, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36332 (p : Pattern) (ha : d15254 p = 1) (hb : d122306 p = 1) : d124758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d122306 q = 1) : d124745 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36331 q ha hb
    | true =>
      simp only [d15244, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d122306 q = 1) : d124746 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36319 q ha hb
    | true =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d122306 q = 1) : d124755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d122306 q = 1) : d124756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d122306 q = 1) : d124757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15254 q = 1) (hb : d122306 q = 1) : d124758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15254, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36333 (p : Pattern) (ha : d15309 p = 1) (hb : d122306 p = 1) : d124687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34646 q ha hb
    | true =>
      simp only [d15160, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15170 q = 1) (hb : d122306 q = 1) : d124681 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d122306, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13287 q = 1) (hb : d122305 q = 1) : d13287 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15304 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15304, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34647 q ha hb
    | true =>
      simp only [d15304, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15305 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15305, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15305, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15306 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15306, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15307 q = 1) (hb : d122306 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15307, d122306, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15308 q = 1) (hb : d122306 q = 1) : d124686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15308, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15309 q = 1) (hb : d122306 q = 1) : d124687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15309, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36334 (p : Pattern) (ha : d15315 p = 1) (hb : d122306 p = 1) : d124768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36333 q ha hb
    | true =>
      simp only [d15310, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d122306 q = 1) : d124765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d122306 q = 1) : d124766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d122306 q = 1) : d124767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15315 q = 1) (hb : d122306 q = 1) : d124768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15315, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36335 (p : Pattern) (ha : d122306 p = 1) (hb : d125617 p = 1) : d124774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d122306 q = 1) : d124725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36327 q ha hb
    | true =>
      simp only [d15215, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36328 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d122306 q = 1) : d124726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d122306 q = 1) : d124727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d122306 q = 1) : d124728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d122306 q = 1) : d124735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36329 q ha hb
    | true =>
      simp only [d15225, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36330 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d122306 q = 1) : d124736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d122306 q = 1) : d124737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d122306 q = 1) : d124763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36332 q ha hb
    | true =>
      simp only [d15259, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36320 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125613 q = 1) : d124764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125613, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d122306 q = 1) : d124769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36334 q ha hb
    | true =>
      simp only [d15316, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d122306 q = 1) : d124770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125614 q = 1) : d124771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125615 q = 1) : d124772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125615, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125616 q = 1) : d124773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125616, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125617 q = 1) : d124774 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125617, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36336 (p : Pattern) (ha : d15322 p = 1) (hb : d122306 p = 1) : d124775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36311 q ha hb
    | true =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d122306 q = 1) : d124695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d122306 q = 1) : d124721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15322 q = 1) (hb : d122306 q = 1) : d124775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15322, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36337 (p : Pattern) (ha : d15323 p = 1) (hb : d122306 p = 1) : d124776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d122306 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d122306 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15323 q = 1) (hb : d122306 q = 1) : d124776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15323, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36338 (p : Pattern) (ha : d15328 p = 1) (hb : d122306 p = 1) : d124781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36311 q ha hb
    | true =>
      simp only [d15178, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d122306 q = 1) : d124694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d122306 q = 1) : d124729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d122306 q = 1) : d124730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15328 q = 1) (hb : d122306 q = 1) : d124781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15328, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36339 (p : Pattern) (ha : d15329 p = 1) (hb : d122306 p = 1) : d124782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d122306 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d122306 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d122306 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15329 q = 1) (hb : d122306 q = 1) : d124782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15329, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36340 (p : Pattern) (ha : d15333 p = 1) (hb : d122306 p = 1) : d124786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d122306 q = 1) : d124745 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36331 q ha hb
    | true =>
      simp only [d15244, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d122306 q = 1) : d124746 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36319 q ha hb
    | true =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d122306 q = 1) : d124755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d122306 q = 1) : d124756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d122306 q = 1) : d124757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15333 q = 1) (hb : d122306 q = 1) : d124786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15333, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36341 (p : Pattern) (ha : d15334 p = 1) (hb : d122306 p = 1) : d124787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d122306 q = 1) : d124753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36319 q ha hb
    | true =>
      simp only [d15249, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d122306 q = 1) : d124754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d122306 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36312 q ha hb
    | true =>
      simp only [d15182, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d122306 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d122306 q = 1) : d124759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d122306 q = 1) : d124760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d122306 q = 1) : d124761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15334 q = 1) (hb : d122306 q = 1) : d124787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15334, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36342 (p : Pattern) (ha : d15340 p = 1) (hb : d122306 p = 1) : d124790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d122306 q = 1) : d124688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36333 q ha hb
    | true =>
      simp only [d15310, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d122306 q = 1) : d124689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d122306 q = 1) : d124765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d122306 q = 1) : d124766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d122306 q = 1) : d124767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15340 q = 1) (hb : d122306 q = 1) : d124790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15340, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36343 (p : Pattern) (ha : d122306 p = 1) (hb : d125622 p = 1) : d124796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d122306 q = 1) : d124725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36327 q ha hb
    | true =>
      simp only [d15215, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36328 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d122306 q = 1) : d124726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d122306 q = 1) : d124727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d122306 q = 1) : d124728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d122306 q = 1) : d124735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36329 q ha hb
    | true =>
      simp only [d15225, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36330 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d122306 q = 1) : d124736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d122306 q = 1) : d124737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d122306 q = 1) : d124763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36332 q ha hb
    | true =>
      simp only [d15259, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36320 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125613 q = 1) : d124764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125613, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d122306 q = 1) : d124769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36334 q ha hb
    | true =>
      simp only [d15316, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d122306 q = 1) : d124770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125614 q = 1) : d124771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125615 q = 1) : d124772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125615, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125616 q = 1) : d124773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125616, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15324 q = 1) (hb : d122306 q = 1) : d124777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36336 q ha hb
    | true =>
      simp only [d15324, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36337 q ha hb
  have h16 (q : Pattern) (ha : d15325 q = 1) (hb : d122306 q = 1) : d124778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15325, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15326 q = 1) (hb : d122306 q = 1) : d124779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15326, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15327 q = 1) (hb : d122306 q = 1) : d124780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15327, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15330 q = 1) (hb : d122306 q = 1) : d124783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36338 q ha hb
    | true =>
      simp only [d15330, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36339 q ha hb
  have h20 (q : Pattern) (ha : d15331 q = 1) (hb : d122306 q = 1) : d124784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15331, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15332 q = 1) (hb : d122306 q = 1) : d124785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15332, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15335 q = 1) (hb : d122306 q = 1) : d124788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36340 q ha hb
    | true =>
      simp only [d15335, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36341 q ha hb
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125618 q = 1) : d124789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125618, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d15341 q = 1) (hb : d122306 q = 1) : d124791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36342 q ha hb
    | true =>
      simp only [d15341, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15342 q = 1) (hb : d122306 q = 1) : d124792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15342, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122306 q = 1) (hb : d125619 q = 1) : d124793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125619, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122306 q = 1) (hb : d125620 q = 1) : d124794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125620, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122306 q = 1) (hb : d125621 q = 1) : d124795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125621, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122306 q = 1) (hb : d125622 q = 1) : d124796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125622, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36344 (p : Pattern) (ha : d122306 p = 1) (hb : d125629 p = 1) : d124821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15335 q = 1) (hb : d122306 q = 1) : d124788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36340 q ha hb
    | true =>
      simp only [d15335, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36341 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125618 q = 1) : d124789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125618, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15341 q = 1) (hb : d122306 q = 1) : d124791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36342 q ha hb
    | true =>
      simp only [d15341, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15342 q = 1) (hb : d122306 q = 1) : d124792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15342, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125619 q = 1) : d124793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125619, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125627 q = 1) : d124819 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125627, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125628 q = 1) : d124820 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125628, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125629 q = 1) : d124821 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125629, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36345 (p : Pattern) (ha : d15423 p = 1) (hb : d122306 p = 1) : d124841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15393 q = 1) (hb : d122305 q = 1) : d124831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15393, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34688 q ha hb
    | true =>
      simp only [d15393, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
  have h2 (q : Pattern) (ha : d15394 q = 1) (hb : d122305 q = 1) : d124832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15394, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15394, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15395 q = 1) (hb : d122305 q = 1) : d124833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15395, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15405 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15406 q = 1) (hb : d122306 q = 1) : d124834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, d122306, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15406, d122306, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h7 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15420 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15421 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15422 q = 1) (hb : d122306 q = 1) : d124840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15422, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15423 q = 1) (hb : d122306 q = 1) : d124841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15423, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36346 (p : Pattern) (ha : d15428 p = 1) (hb : d122306 p = 1) : d124849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15421 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15418 q = 1) (hb : d122305 q = 1) : d124844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15418, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34691 q ha hb
  have h7 (q : Pattern) (ha : d15419 q = 1) (hb : d122305 q = 1) : d124845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15420 q = 1) (hb : d122305 q = 1) : d124846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15426 q = 1) (hb : d122306 q = 1) : d124847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, d122306, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15426, d122306, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15427 q = 1) (hb : d122306 q = 1) : d124848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15427, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15428 q = 1) (hb : d122306 q = 1) : d124849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15428, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36347 (p : Pattern) (ha : d15434 p = 1) (hb : d122306 p = 1) : d124855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15424 q = 1) (hb : d122306 q = 1) : d124842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36345 q ha hb
    | true =>
      simp only [d15424, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15425 q = 1) (hb : d122306 q = 1) : d124843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15425, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15429 q = 1) (hb : d122306 q = 1) : d124850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36346 q ha hb
    | true =>
      simp only [d15429, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15430 q = 1) (hb : d122306 q = 1) : d124851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15431 q = 1) (hb : d122306 q = 1) : d124852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15431, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15432 q = 1) (hb : d122306 q = 1) : d124853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15432, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15433 q = 1) (hb : d122306 q = 1) : d124854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15433, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15434 q = 1) (hb : d122306 q = 1) : d124855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15434, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36348 (p : Pattern) (ha : d15447 p = 1) (hb : d122306 p = 1) : d124867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15429 q = 1) (hb : d122306 q = 1) : d124850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36346 q ha hb
    | true =>
      simp only [d15429, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15430 q = 1) (hb : d122306 q = 1) : d124851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d122306 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36324 q ha hb
    | true =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d122306 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15444 q = 1) (hb : d122306 q = 1) : d124864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15444, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15445 q = 1) (hb : d122306 q = 1) : d124865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15445, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15446 q = 1) (hb : d122306 q = 1) : d124866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15446, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15447 q = 1) (hb : d122306 q = 1) : d124867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15447, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36349 (p : Pattern) (ha : d15504 p = 1) (hb : d122306 p = 1) : d124871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15421 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13516 q = 1) (hb : d122305 q = 1) : d13516 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15499 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15499, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15499, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15500 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15500, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15500, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15501 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15501, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15502 q = 1) (hb : d122306 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15502, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15503 q = 1) (hb : d122306 q = 1) : d124870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15503, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15504 q = 1) (hb : d122306 q = 1) : d124871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15504, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36350 (p : Pattern) (ha : d15510 p = 1) (hb : d122306 p = 1) : d124877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15505 q = 1) (hb : d122306 q = 1) : d124872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36349 q ha hb
    | true =>
      simp only [d15505, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15506 q = 1) (hb : d122306 q = 1) : d124873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15506, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15507 q = 1) (hb : d122306 q = 1) : d124874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15507, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15508 q = 1) (hb : d122306 q = 1) : d124875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15508, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15509 q = 1) (hb : d122306 q = 1) : d124876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15509, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15510 q = 1) (hb : d122306 q = 1) : d124877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15510, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36351 (p : Pattern) (ha : d122306 p = 1) (hb : d125639 p = 1) : d124883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15448 q = 1) (hb : d122306 q = 1) : d124868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36347 q ha hb
    | true =>
      simp only [d15448, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36348 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125635 q = 1) : d124869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125635, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15511 q = 1) (hb : d122306 q = 1) : d124878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36350 q ha hb
    | true =>
      simp only [d15511, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15512 q = 1) (hb : d122306 q = 1) : d124879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15512, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125636 q = 1) : d124880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125636, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125637 q = 1) : d124881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125637, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125638 q = 1) : d124882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125638, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125639 q = 1) : d124883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125639, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36352 (p : Pattern) (ha : d122306 p = 1) (hb : d125645 p = 1) : d124900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15198 q = 1) (hb : d122306 q = 1) : d124708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15198, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36315 q ha hb
  have h2 (q : Pattern) (ha : d15199 q = 1) (hb : d122306 q = 1) : d124709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15199, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15208 q = 1) (hb : d122306 q = 1) : d124718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36315 q ha hb
    | true =>
      simp only [d15208, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36318 q ha hb
  have h4 (q : Pattern) (ha : d15209 q = 1) (hb : d122306 q = 1) : d124719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15209, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15210 q = 1) (hb : d122306 q = 1) : d124720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15210, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125623 q = 1) : d124797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36335 q ha hb
    | true =>
      simp only [d125623, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36343 q ha hb
  have h7 (q : Pattern) (ha : d15365 q = 1) (hb : d122306 q = 1) : d124815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36321 q ha hb
    | true =>
      simp only [d15365, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36322 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125624 q = 1) : d124816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125624, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125625 q = 1) : d124817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125625, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125626 q = 1) : d124818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125626, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125630 q = 1) : d124822 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125630, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36344 q ha hb
  have h12 (q : Pattern) (ha : d15374 q = 1) (hb : d122306 q = 1) : d124824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15374, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36323 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125631 q = 1) : d124825 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125631, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125632 q = 1) : d124826 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125632, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125633 q = 1) : d124827 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125633, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125634 q = 1) : d124828 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125634, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125640 q = 1) : d124884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125640, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36351 q ha hb
  have h18 (q : Pattern) (ha : d15528 q = 1) (hb : d122306 q = 1) : d124895 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15528, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36326 q ha hb
  have h19 (q : Pattern) (ha : d122306 q = 1) (hb : d125641 q = 1) : d124896 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125641, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122306 q = 1) (hb : d125642 q = 1) : d124897 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125642, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122306 q = 1) (hb : d125643 q = 1) : d124898 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125643, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122306 q = 1) (hb : d125644 q = 1) : d124899 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125644, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125645 q = 1) : d124900 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125645, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36353 (p : Pattern) (ha : d122306 p = 1) (hb : d125651 p = 1) : d124906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125646 q = 1) : d124901 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125646, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36352 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125647 q = 1) : d124902 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125647, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125648 q = 1) : d124903 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125648, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125649 q = 1) : d124904 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125649, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125650 q = 1) : d124905 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125650, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125651 q = 1) : d124906 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125651, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36354 (p : Pattern) (ha : d15569 p = 1) (hb : d122306 p = 1) : d124922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15562 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15564 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34704 q ha hb
  have h7 (q : Pattern) (ha : d15565 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15566 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15567 q = 1) (hb : d122306 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15567, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15568 q = 1) (hb : d122306 q = 1) : d124921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15568, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15569 q = 1) (hb : d122306 q = 1) : d124922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15569, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36355 (p : Pattern) (ha : d15573 p = 1) (hb : d122306 p = 1) : d124926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15564 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15564, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34704 q ha hb
  have h2 (q : Pattern) (ha : d15565 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15566 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15567 q = 1) (hb : d122306 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15567, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15572 q = 1) (hb : d122306 q = 1) : d124925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15572, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15573 q = 1) (hb : d122306 q = 1) : d124926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15573, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro36356 (p : Pattern) (ha : d15579 p = 1) (hb : d122306 p = 1) : d124932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36354 q ha hb
    | true =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d122306 q = 1) : d124931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15579 q = 1) (hb : d122306 q = 1) : d124932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15579, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36357 (p : Pattern) (ha : d15583 p = 1) (hb : d122306 p = 1) : d124936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d122306 q = 1) : d124935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15583 q = 1) (hb : d122306 q = 1) : d124936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15583, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36358 (p : Pattern) (ha : d15589 p = 1) (hb : d122306 p = 1) : d124942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d122306 q = 1) : d124937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36356 q ha hb
    | true =>
      simp only [d15584, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36357 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d122306 q = 1) : d124938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d122306 q = 1) : d124939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d122306 q = 1) : d124940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d122306 q = 1) : d124941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15589 q = 1) (hb : d122306 q = 1) : d124942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36359 (p : Pattern) (ha : d15592 p = 1) (hb : d122306 p = 1) : d124945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36354 q ha hb
    | true =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d122306 q = 1) : d124931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15592 q = 1) (hb : d122306 q = 1) : d124945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15592, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36360 (p : Pattern) (ha : d15593 p = 1) (hb : d122306 p = 1) : d124946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d122306 q = 1) : d124935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15593 q = 1) (hb : d122306 q = 1) : d124946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15593, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36361 (p : Pattern) (ha : d15599 p = 1) (hb : d122306 p = 1) : d124952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d122306 q = 1) : d124937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36356 q ha hb
    | true =>
      simp only [d15584, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36357 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d122306 q = 1) : d124938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d122306 q = 1) : d124939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d122306 q = 1) : d124940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d122306 q = 1) : d124941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15594 q = 1) (hb : d122306 q = 1) : d124947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36359 q ha hb
    | true =>
      simp only [d15594, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36360 q ha hb
  have h7 (q : Pattern) (ha : d15595 q = 1) (hb : d122306 q = 1) : d124948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15596 q = 1) (hb : d122306 q = 1) : d124949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15596, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15597 q = 1) (hb : d122306 q = 1) : d124950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15598 q = 1) (hb : d122306 q = 1) : d124951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15599 q = 1) (hb : d122306 q = 1) : d124952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15599, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36362 (p : Pattern) (ha : d15636 p = 1) (hb : d122306 p = 1) : d124986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15562 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15559 q = 1) (hb : d122305 q = 1) : d124981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15559, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34703 q ha hb
  have h7 (q : Pattern) (ha : d15560 q = 1) (hb : d122305 q = 1) : d124982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15561 q = 1) (hb : d122305 q = 1) : d124983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15634 q = 1) (hb : d122306 q = 1) : d124984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, d122306, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15634, d122306, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15635 q = 1) (hb : d122306 q = 1) : d124985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15635, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15636 q = 1) (hb : d122306 q = 1) : d124986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15636, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36363 (p : Pattern) (ha : d15646 p = 1) (hb : d122306 p = 1) : d124996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36362 q ha hb
    | true =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d122306 q = 1) : d124993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d122306 q = 1) : d124994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d122306 q = 1) : d124995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15646 q = 1) (hb : d122306 q = 1) : d124996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15646, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36364 (p : Pattern) (ha : d15746 p = 1) (hb : d122306 p = 1) : d125042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15736 q = 1) (hb : d122306 q = 1) : d125032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36363 q ha hb
    | true =>
      simp only [d15736, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36357 q ha hb
  have h2 (q : Pattern) (ha : d15737 q = 1) (hb : d122306 q = 1) : d125033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15737, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15738 q = 1) (hb : d122306 q = 1) : d125034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15738, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15739 q = 1) (hb : d122306 q = 1) : d125035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15739, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15740 q = 1) (hb : d122306 q = 1) : d125036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15740, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15741 q = 1) (hb : d122306 q = 1) : d125037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36357 q ha hb
    | true =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15742 q = 1) (hb : d122306 q = 1) : d125038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15743 q = 1) (hb : d122306 q = 1) : d125039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15744 q = 1) (hb : d122306 q = 1) : d125040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15745 q = 1) (hb : d122306 q = 1) : d125041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15746 q = 1) (hb : d122306 q = 1) : d125042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15746, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36365 (p : Pattern) (ha : d15752 p = 1) (hb : d122306 p = 1) : d125048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15741 q = 1) (hb : d122306 q = 1) : d125037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36357 q ha hb
    | true =>
      simp only [d15741, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15742 q = 1) (hb : d122306 q = 1) : d125038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15743 q = 1) (hb : d122306 q = 1) : d125039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15743, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15744 q = 1) (hb : d122306 q = 1) : d125040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15745 q = 1) (hb : d122306 q = 1) : d125041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15747 q = 1) (hb : d122306 q = 1) : d125043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36360 q ha hb
    | true =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15748 q = 1) (hb : d122306 q = 1) : d125044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15749 q = 1) (hb : d122306 q = 1) : d125045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15750 q = 1) (hb : d122306 q = 1) : d125046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15751 q = 1) (hb : d122306 q = 1) : d125047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15752 q = 1) (hb : d122306 q = 1) : d125048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15752, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36366 (p : Pattern) (ha : d15761 p = 1) (hb : d122306 p = 1) : d125057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15747 q = 1) (hb : d122306 q = 1) : d125043 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36360 q ha hb
    | true =>
      simp only [d15747, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15748 q = 1) (hb : d122306 q = 1) : d125044 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15749 q = 1) (hb : d122306 q = 1) : d125045 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15749, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15750 q = 1) (hb : d122306 q = 1) : d125046 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15751 q = 1) (hb : d122306 q = 1) : d125047 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15761 q = 1) (hb : d122306 q = 1) : d125057 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15761, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36367 (p : Pattern) (ha : d15819 p = 1) (hb : d122306 p = 1) : d125094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15814 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15814, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34719 q ha hb
  have h2 (q : Pattern) (ha : d15815 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15816 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15817 q = 1) (hb : d122306 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15817, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15818 q = 1) (hb : d122306 q = 1) : d125093 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15818, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15819 q = 1) (hb : d122306 q = 1) : d125094 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15819, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro36368 (p : Pattern) (ha : d15899 p = 1) (hb : d122306 p = 1) : d125121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15820 q = 1) (hb : d122306 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36367 q ha hb
    | true =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15821 q = 1) (hb : d122306 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15896 q = 1) (hb : d122306 q = 1) : d125118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15896, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15897 q = 1) (hb : d122306 q = 1) : d125119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15897, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15898 q = 1) (hb : d122306 q = 1) : d125120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15898, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15899 q = 1) (hb : d122306 q = 1) : d125121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15899, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36369 (p : Pattern) (ha : d15905 p = 1) (hb : d122306 p = 1) : d125127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15900 q = 1) (hb : d122306 q = 1) : d125122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36368 q ha hb
    | true =>
      simp only [d15900, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15901 q = 1) (hb : d122306 q = 1) : d125123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15901, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15902 q = 1) (hb : d122306 q = 1) : d125124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15902, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15903 q = 1) (hb : d122306 q = 1) : d125125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15903, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15904 q = 1) (hb : d122306 q = 1) : d125126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15904, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15905 q = 1) (hb : d122306 q = 1) : d125127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15905, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36370 (p : Pattern) (ha : d15604 p = 1) (hb : d122306 p = 1) : d124957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36354 q ha hb
    | true =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d122306 q = 1) : d124956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15604 q = 1) (hb : d122306 q = 1) : d124957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15604, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36371 (p : Pattern) (ha : d15606 p = 1) (hb : d122306 p = 1) : d124959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d122306 q = 1) : d124958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15606 q = 1) (hb : d122306 q = 1) : d124959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15606, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36372 (p : Pattern) (ha : d15613 p = 1) (hb : d122306 p = 1) : d124966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36354 q ha hb
    | true =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d122306 q = 1) : d124964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d122306 q = 1) : d124965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15613 q = 1) (hb : d122306 q = 1) : d124966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15613, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36373 (p : Pattern) (ha : d15616 p = 1) (hb : d122306 p = 1) : d124969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d122306 q = 1) : d124967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d122306 q = 1) : d124968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15616 q = 1) (hb : d122306 q = 1) : d124969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15616, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36374 (p : Pattern) (ha : d15631 p = 1) (hb : d122306 p = 1) : d124978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15621 q = 1) (hb : d122305 q = 1) : d15621 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15622 q = 1) (hb : d122305 q = 1) : d124973 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15622, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15622, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
  have h3 (q : Pattern) (ha : d15623 q = 1) (hb : d122305 q = 1) : d124974 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15623, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15623, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15624 q = 1) (hb : d122305 q = 1) : d124975 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15624, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15628 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15629 q = 1) (hb : d122306 q = 1) : d124976 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, d122306, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15629, d122306, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h8 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15561 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15562 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15630 q = 1) (hb : d122306 q = 1) : d124977 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15630, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15631 q = 1) (hb : d122306 q = 1) : d124978 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15631, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36375 (p : Pattern) (ha : d15642 p = 1) (hb : d122306 p = 1) : d124992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d122306 q = 1) : d124979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36374 q ha hb
    | true =>
      simp only [d15632, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d122306 q = 1) : d124980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36362 q ha hb
    | true =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d122306 q = 1) : d124989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d122306 q = 1) : d124990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d122306 q = 1) : d124991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15642 q = 1) (hb : d122306 q = 1) : d124992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15642, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36376 (p : Pattern) (ha : d15697 p = 1) (hb : d122306 p = 1) : d124922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d122305 q = 1) : d124913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34701 q ha hb
    | true =>
      simp only [d15552, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d122305 q = 1) : d124914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d122305 q = 1) : d124915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15562 q = 1) (hb : d122306 q = 1) : d124916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d122306, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13614 q = 1) (hb : d122305 q = 1) : d13614 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15692 q = 1) (hb : d122305 q = 1) : d124917 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15692, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34702 q ha hb
    | true =>
      simp only [d15692, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15693 q = 1) (hb : d122305 q = 1) : d124918 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15693, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15693, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15694 q = 1) (hb : d122305 q = 1) : d124919 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15694, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15695 q = 1) (hb : d122306 q = 1) : d124920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15695, d122306, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15696 q = 1) (hb : d122306 q = 1) : d124921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15696, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15697 q = 1) (hb : d122306 q = 1) : d124922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15697, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36377 (p : Pattern) (ha : d15703 p = 1) (hb : d122306 p = 1) : d125002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36376 q ha hb
    | true =>
      simp only [d15698, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d122306 q = 1) : d124999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d122306 q = 1) : d125000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d122306 q = 1) : d125001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15703 q = 1) (hb : d122306 q = 1) : d125002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15703, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36378 (p : Pattern) (ha : d122306 p = 1) (hb : d125660 p = 1) : d125008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d122306 q = 1) : d124960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36370 q ha hb
    | true =>
      simp only [d15607, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36371 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d122306 q = 1) : d124961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d122306 q = 1) : d124962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d122306 q = 1) : d124963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d122306 q = 1) : d124970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36372 q ha hb
    | true =>
      simp only [d15617, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36373 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d122306 q = 1) : d124971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d122306 q = 1) : d124972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d122306 q = 1) : d124997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36375 q ha hb
    | true =>
      simp only [d15647, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36363 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125656 q = 1) : d124998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125656, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d122306 q = 1) : d125003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36377 q ha hb
    | true =>
      simp only [d15704, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d122306 q = 1) : d125004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125657 q = 1) : d125005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125658 q = 1) : d125006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125658, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125659 q = 1) : d125007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125659, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125660 q = 1) : d125008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125660, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36379 (p : Pattern) (ha : d15710 p = 1) (hb : d122306 p = 1) : d125009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36354 q ha hb
    | true =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d122306 q = 1) : d124930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d122306 q = 1) : d124956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15710 q = 1) (hb : d122306 q = 1) : d125009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15710, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36380 (p : Pattern) (ha : d15711 p = 1) (hb : d122306 p = 1) : d125010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d122306 q = 1) : d124934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d122306 q = 1) : d124958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15711 q = 1) (hb : d122306 q = 1) : d125010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15711, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36381 (p : Pattern) (ha : d15716 p = 1) (hb : d122306 p = 1) : d125015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36354 q ha hb
    | true =>
      simp only [d15570, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d122306 q = 1) : d124929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d122306 q = 1) : d124964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d122306 q = 1) : d124965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15716 q = 1) (hb : d122306 q = 1) : d125015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15716, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36382 (p : Pattern) (ha : d15717 p = 1) (hb : d122306 p = 1) : d125016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d122306 q = 1) : d124933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d122306 q = 1) : d124967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d122306 q = 1) : d124968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15717 q = 1) (hb : d122306 q = 1) : d125016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15717, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36383 (p : Pattern) (ha : d15721 p = 1) (hb : d122306 p = 1) : d125020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d122306 q = 1) : d124979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36374 q ha hb
    | true =>
      simp only [d15632, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d122306 q = 1) : d124980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36362 q ha hb
    | true =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d122306 q = 1) : d124989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d122306 q = 1) : d124990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d122306 q = 1) : d124991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15721 q = 1) (hb : d122306 q = 1) : d125020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15721, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36384 (p : Pattern) (ha : d15722 p = 1) (hb : d122306 p = 1) : d125021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d122306 q = 1) : d124987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36362 q ha hb
    | true =>
      simp only [d15637, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d122306 q = 1) : d124988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d122306 q = 1) : d124927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36355 q ha hb
    | true =>
      simp only [d15574, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d122306 q = 1) : d124928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d122306 q = 1) : d124993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d122306 q = 1) : d124994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d122306 q = 1) : d124995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15722 q = 1) (hb : d122306 q = 1) : d125021 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15722, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36385 (p : Pattern) (ha : d15728 p = 1) (hb : d122306 p = 1) : d125024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d122306 q = 1) : d124923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36376 q ha hb
    | true =>
      simp only [d15698, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d122306 q = 1) : d124924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d122306 q = 1) : d124999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d122306 q = 1) : d125000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d122306 q = 1) : d125001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15728 q = 1) (hb : d122306 q = 1) : d125024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15728, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36386 (p : Pattern) (ha : d122306 p = 1) (hb : d125665 p = 1) : d125030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d122306 q = 1) : d124960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36370 q ha hb
    | true =>
      simp only [d15607, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36371 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d122306 q = 1) : d124961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d122306 q = 1) : d124962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d122306 q = 1) : d124963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d122306 q = 1) : d124970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36372 q ha hb
    | true =>
      simp only [d15617, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36373 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d122306 q = 1) : d124971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d122306 q = 1) : d124972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d122306 q = 1) : d124997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36375 q ha hb
    | true =>
      simp only [d15647, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36363 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125656 q = 1) : d124998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125656, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d122306 q = 1) : d125003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36377 q ha hb
    | true =>
      simp only [d15704, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d122306 q = 1) : d125004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125657 q = 1) : d125005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125658 q = 1) : d125006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125658, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125659 q = 1) : d125007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125659, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15712 q = 1) (hb : d122306 q = 1) : d125011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36379 q ha hb
    | true =>
      simp only [d15712, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36380 q ha hb
  have h16 (q : Pattern) (ha : d15713 q = 1) (hb : d122306 q = 1) : d125012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15713, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15714 q = 1) (hb : d122306 q = 1) : d125013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15714, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15715 q = 1) (hb : d122306 q = 1) : d125014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15715, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15718 q = 1) (hb : d122306 q = 1) : d125017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36381 q ha hb
    | true =>
      simp only [d15718, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36382 q ha hb
  have h20 (q : Pattern) (ha : d15719 q = 1) (hb : d122306 q = 1) : d125018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15719, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15720 q = 1) (hb : d122306 q = 1) : d125019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15720, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15723 q = 1) (hb : d122306 q = 1) : d125022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36383 q ha hb
    | true =>
      simp only [d15723, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36384 q ha hb
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125661 q = 1) : d125023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125661, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d15729 q = 1) (hb : d122306 q = 1) : d125025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36385 q ha hb
    | true =>
      simp only [d15729, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15730 q = 1) (hb : d122306 q = 1) : d125026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15730, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122306 q = 1) (hb : d125662 q = 1) : d125027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125662, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122306 q = 1) (hb : d125663 q = 1) : d125028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125663, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122306 q = 1) (hb : d125664 q = 1) : d125029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125664, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122306 q = 1) (hb : d125665 q = 1) : d125030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125665, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36387 (p : Pattern) (ha : d122306 p = 1) (hb : d125672 p = 1) : d125055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15723 q = 1) (hb : d122306 q = 1) : d125022 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36383 q ha hb
    | true =>
      simp only [d15723, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36384 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125661 q = 1) : d125023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125661, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15729 q = 1) (hb : d122306 q = 1) : d125025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36385 q ha hb
    | true =>
      simp only [d15729, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15730 q = 1) (hb : d122306 q = 1) : d125026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15730, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125662 q = 1) : d125027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125662, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125670 q = 1) : d125053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125670, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125671 q = 1) : d125054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125671, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125672 q = 1) : d125055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125672, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36388 (p : Pattern) (ha : d15801 p = 1) (hb : d122306 p = 1) : d125074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15768 q = 1) (hb : d122305 q = 1) : d15768 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15772 q = 1) (hb : d122305 q = 1) : d125064 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15772, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15772, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
  have h3 (q : Pattern) (ha : d15773 q = 1) (hb : d122305 q = 1) : d125065 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15773, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15773, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15774 q = 1) (hb : d122305 q = 1) : d125066 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15774, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15783 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15784 q = 1) (hb : d122306 q = 1) : d125067 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, d122306, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15784, d122306, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h8 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15798 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15799 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15800 q = 1) (hb : d122306 q = 1) : d125073 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15800, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15801 q = 1) (hb : d122306 q = 1) : d125074 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15801, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36389 (p : Pattern) (ha : d15806 p = 1) (hb : d122306 p = 1) : d125082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15798 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15799 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15796 q = 1) (hb : d122305 q = 1) : d125077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15796, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34744 q ha hb
  have h7 (q : Pattern) (ha : d15797 q = 1) (hb : d122305 q = 1) : d125078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15798 q = 1) (hb : d122305 q = 1) : d125079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15804 q = 1) (hb : d122306 q = 1) : d125080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, d122306, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15804, d122306, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15805 q = 1) (hb : d122306 q = 1) : d125081 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15805, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15806 q = 1) (hb : d122306 q = 1) : d125082 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15806, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36390 (p : Pattern) (ha : d15812 p = 1) (hb : d122306 p = 1) : d125088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15802 q = 1) (hb : d122306 q = 1) : d125075 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36388 q ha hb
    | true =>
      simp only [d15802, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15803 q = 1) (hb : d122306 q = 1) : d125076 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15803, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15807 q = 1) (hb : d122306 q = 1) : d125083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36389 q ha hb
    | true =>
      simp only [d15807, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15808 q = 1) (hb : d122306 q = 1) : d125084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15809 q = 1) (hb : d122306 q = 1) : d125085 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15809, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15810 q = 1) (hb : d122306 q = 1) : d125086 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15810, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15811 q = 1) (hb : d122306 q = 1) : d125087 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15811, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15812 q = 1) (hb : d122306 q = 1) : d125088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15812, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36391 (p : Pattern) (ha : d15825 p = 1) (hb : d122306 p = 1) : d125100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15807 q = 1) (hb : d122306 q = 1) : d125083 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36389 q ha hb
    | true =>
      simp only [d15807, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15808 q = 1) (hb : d122306 q = 1) : d125084 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d122306 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36367 q ha hb
    | true =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d122306 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15822 q = 1) (hb : d122306 q = 1) : d125097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15822, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15823 q = 1) (hb : d122306 q = 1) : d125098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15823, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15824 q = 1) (hb : d122306 q = 1) : d125099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15824, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15825 q = 1) (hb : d122306 q = 1) : d125100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15825, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36392 (p : Pattern) (ha : d15882 p = 1) (hb : d122306 p = 1) : d125104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15798 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15799 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13843 q = 1) (hb : d122305 q = 1) : d13843 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15877 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15877, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15877, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15878 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15878, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15878, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15879 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15879, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15880 q = 1) (hb : d122306 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15880, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15881 q = 1) (hb : d122306 q = 1) : d125103 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15881, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15882 q = 1) (hb : d122306 q = 1) : d125104 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15882, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36393 (p : Pattern) (ha : d15888 p = 1) (hb : d122306 p = 1) : d125110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15883 q = 1) (hb : d122306 q = 1) : d125105 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15883, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36392 q ha hb
    | true =>
      simp only [d15883, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15884 q = 1) (hb : d122306 q = 1) : d125106 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15884, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15884, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15885 q = 1) (hb : d122306 q = 1) : d125107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15885, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15885, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15886 q = 1) (hb : d122306 q = 1) : d125108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15886, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15886, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15887 q = 1) (hb : d122306 q = 1) : d125109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15887, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15887, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15888 q = 1) (hb : d122306 q = 1) : d125110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15888, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15888, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36394 (p : Pattern) (ha : d122306 p = 1) (hb : d125682 p = 1) : d125116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15826 q = 1) (hb : d122306 q = 1) : d125101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15826, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36390 q ha hb
    | true =>
      simp only [d15826, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36391 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125678 q = 1) : d125102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125678, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d15889 q = 1) (hb : d122306 q = 1) : d125111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15889, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36393 q ha hb
    | true =>
      simp only [d15889, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15890 q = 1) (hb : d122306 q = 1) : d125112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15890, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15890, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125679 q = 1) : d125113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125679, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125680 q = 1) : d125114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125680, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125681 q = 1) : d125115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125681, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125682 q = 1) : d125116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125682, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36395 (p : Pattern) (ha : d122306 p = 1) (hb : d125688 p = 1) : d125133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15590 q = 1) (hb : d122306 q = 1) : d124943 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15590, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15590, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36358 q ha hb
  have h2 (q : Pattern) (ha : d15591 q = 1) (hb : d122306 q = 1) : d124944 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15591, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15591, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15600 q = 1) (hb : d122306 q = 1) : d124953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36358 q ha hb
    | true =>
      simp only [d15600, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36361 q ha hb
  have h4 (q : Pattern) (ha : d15601 q = 1) (hb : d122306 q = 1) : d124954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15601, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15602 q = 1) (hb : d122306 q = 1) : d124955 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15602, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15602, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125666 q = 1) : d125031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36378 q ha hb
    | true =>
      simp only [d125666, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36386 q ha hb
  have h7 (q : Pattern) (ha : d15753 q = 1) (hb : d122306 q = 1) : d125049 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15753, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36364 q ha hb
    | true =>
      simp only [d15753, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36365 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125667 q = 1) : d125050 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125667, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125668 q = 1) : d125051 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125668, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125669 q = 1) : d125052 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125669, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125673 q = 1) : d125056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125673, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36387 q ha hb
  have h12 (q : Pattern) (ha : d15762 q = 1) (hb : d122306 q = 1) : d125058 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15762, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15762, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36366 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125674 q = 1) : d125059 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125674, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125675 q = 1) : d125060 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125675, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125676 q = 1) : d125061 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125676, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125677 q = 1) : d125062 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125677, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125683 q = 1) : d125117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125683, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36394 q ha hb
  have h18 (q : Pattern) (ha : d15906 q = 1) (hb : d122306 q = 1) : d125128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15906, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15906, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36369 q ha hb
  have h19 (q : Pattern) (ha : d122306 q = 1) (hb : d125684 q = 1) : d125129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125684, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122306 q = 1) (hb : d125685 q = 1) : d125130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125685, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122306 q = 1) (hb : d125686 q = 1) : d125131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125686, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122306 q = 1) (hb : d125687 q = 1) : d125132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125687, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125688 q = 1) : d125133 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125688, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36396 (p : Pattern) (ha : d122306 p = 1) (hb : d125694 p = 1) : d125139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125689 q = 1) : d125134 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125689, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36395 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125690 q = 1) : d125135 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125690, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125691 q = 1) : d125136 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125691, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125692 q = 1) : d125137 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125692, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125693 q = 1) : d125138 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125693, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125694 q = 1) : d125139 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125694, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36397 (p : Pattern) (ha : d122306 p = 1) (hb : d125700 p = 1) : d125145 p = 1 := by
  have h0 (q : Pattern) (ha : d122306 q = 1) (hb : d125529 q = 1) : d124246 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36191 q ha hb
    | true =>
      simp only [d125529, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36229 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125569 q = 1) : d124440 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125569, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36267 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125570 q = 1) : d124441 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125610 q = 1) : d124673 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125610, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36310 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125611 q = 1) : d124674 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125611, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125612 q = 1) : d124675 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125652 q = 1) : d124907 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125652, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36353 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125653 q = 1) : d124908 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125653, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125654 q = 1) : d124909 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125654, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125655 q = 1) : d124910 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125695 q = 1) : d125140 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125695, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36396 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125696 q = 1) : d125141 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125696, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125697 q = 1) : d125142 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125697, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125698 q = 1) : d125143 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125698, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125699 q = 1) : d125144 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125700 q = 1) : d125145 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro36398 (p : Pattern) (ha : d122306 p = 1) (hb : d125706 p = 1) : d125151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125701 q = 1) : d125146 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36397 q ha hb
    | true =>
      simp only [d125701, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125702 q = 1) : d125147 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125703 q = 1) : d125148 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125704 q = 1) : d125149 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125705 q = 1) : d125150 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125706 q = 1) : d125151 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36399 (p : Pattern) (ha : d122306 p = 1) (hb : d125712 p = 1) : d125157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125707 q = 1) : d125152 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36398 q ha hb
    | true =>
      simp only [d125707, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125708 q = 1) : d125153 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125709 q = 1) : d125154 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125710 q = 1) : d125155 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125711 q = 1) : d125156 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125712 q = 1) : d125157 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36400 (p : Pattern) (ha : d122306 p = 1) (hb : d125718 p = 1) : d125163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125713 q = 1) : d125158 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36399 q ha hb
    | true =>
      simp only [d125713, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125714 q = 1) : d125159 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125715 q = 1) : d125160 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125716 q = 1) : d125161 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125717 q = 1) : d125162 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125718 q = 1) : d125163 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36401 (p : Pattern) (ha : d122306 p = 1) (hb : d125724 p = 1) : d125169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125719 q = 1) : d125164 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36400 q ha hb
    | true =>
      simp only [d125719, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125720 q = 1) : d125165 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125721 q = 1) : d125166 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125722 q = 1) : d125167 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125723 q = 1) : d125168 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125724 q = 1) : d125169 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36402 (p : Pattern) (ha : d122306 p = 1) (hb : d125730 p = 1) : d125175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125725 q = 1) : d125170 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36401 q ha hb
    | true =>
      simp only [d125725, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125726 q = 1) : d125171 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125727 q = 1) : d125172 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125728 q = 1) : d125173 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125729 q = 1) : d125174 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125730 q = 1) : d125175 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36403 (p : Pattern) (ha : d122306 p = 1) (hb : d125736 p = 1) : d125181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125731 q = 1) : d125176 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36402 q ha hb
    | true =>
      simp only [d125731, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125732 q = 1) : d125177 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125733 q = 1) : d125178 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125734 q = 1) : d125179 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125735 q = 1) : d125180 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125736 q = 1) : d125181 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36404 (p : Pattern) (ha : d122306 p = 1) (hb : d125742 p = 1) : d125187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125737 q = 1) : d125182 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36403 q ha hb
    | true =>
      simp only [d125737, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125738 q = 1) : d125183 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125739 q = 1) : d125184 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125740 q = 1) : d125185 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125741 q = 1) : d125186 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125742 q = 1) : d125187 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36405 (p : Pattern) (ha : d51995 p = 1) (hb : d123879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13980 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13980, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d51995 q = 1) (hb : d123879 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d51995, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d51995, d123879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36406 (p : Pattern) (ha : d81527 p = 1) (hb : d123885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51996 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51996, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36405 q ha hb
    | true =>
      simp only [d51996, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d51997 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51997, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51997, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51998 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51998, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51998, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52222 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52222, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52222, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d81526 q = 1) (hb : d123884 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81526, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81526, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81527 q = 1) (hb : d123885 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81527, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81527, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36407 (p : Pattern) (ha : d92321 p = 1) (hb : d123891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d123890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92321 q = 1) (hb : d123891 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92321, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92321, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36408 (p : Pattern) (ha : d92327 p = 1) (hb : d123897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d123893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d123894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d123895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d123896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92327 q = 1) (hb : d123897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92327, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92327, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36409 (p : Pattern) (ha : d92328 p = 1) (hb : d123898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d123890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92328 q = 1) (hb : d123898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92328, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92328, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36410 (p : Pattern) (ha : d92334 p = 1) (hb : d123904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d123893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d123894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d123895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d123896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d92329 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
    | true =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92330 q = 1) (hb : d123900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92330, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d92331 q = 1) (hb : d123901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92331, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92332 q = 1) (hb : d123902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92332, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d92332, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92333 q = 1) (hb : d123903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92333, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d92333, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92334 q = 1) (hb : d123904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92334, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92334, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36411 (p : Pattern) (ha : d92341 p = 1) (hb : d123911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92329 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
    | true =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92330 q = 1) (hb : d123900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92330, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92331 q = 1) (hb : d123901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92331, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92339 q = 1) (hb : d123909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92339, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92339, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92340 q = 1) (hb : d123910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92340, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92340, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92341 q = 1) (hb : d123911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92341, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92341, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36412 (p : Pattern) (ha : d52049 p = 1) (hb : d123917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14019 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14019, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52049 q = 1) (hb : d123917 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52049, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52049, d123917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36413 (p : Pattern) (ha : d81560 p = 1) (hb : d123923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52050 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36412 q ha hb
    | true =>
      simp only [d52050, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d52051 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52052 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52377 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52377, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52377, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d81559 q = 1) (hb : d123922 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81559, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81559, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81560 q = 1) (hb : d123923 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81560, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81560, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36414 (p : Pattern) (ha : d92350 p = 1) (hb : d123929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81561 q = 1) (hb : d123924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36413 q ha hb
    | true =>
      simp only [d81561, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81562 q = 1) (hb : d123925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92347 q = 1) (hb : d123926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92347, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92347, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92348 q = 1) (hb : d123927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92348, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92348, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92349 q = 1) (hb : d123928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92349, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92349, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92350 q = 1) (hb : d123929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92350, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92350, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36415 (p : Pattern) (ha : d92356 p = 1) (hb : d123935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92351 q = 1) (hb : d123930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36414 q ha hb
    | true =>
      simp only [d92351, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92352 q = 1) (hb : d123931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92352, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92352, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92353 q = 1) (hb : d123932 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92353, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92353, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92354 q = 1) (hb : d123933 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92354, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92354, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92355 q = 1) (hb : d123934 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92355, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92355, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92356 q = 1) (hb : d123935 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92356, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92356, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36416 (p : Pattern) (ha : d92362 p = 1) (hb : d123941 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d92335 q = 1) (hb : d123905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92335, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36408 q ha hb
    | true =>
      simp only [d92335, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36410 q ha hb
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
  have h8 (q : Pattern) (ha : d92336 q = 1) (hb : d123906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92336, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92336, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d92337 q = 1) (hb : d123907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92337, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92337, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92338 q = 1) (hb : d123908 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92338, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d92338, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92342 q = 1) (hb : d123912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92342, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92342, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36411 q ha hb
  have h12 (q : Pattern) (ha : d92343 q = 1) (hb : d123913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92343, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92343, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92344 q = 1) (hb : d123914 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92344, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92344, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92345 q = 1) (hb : d123915 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92345, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92345, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92346 q = 1) (hb : d123916 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92346, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92346, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92357 q = 1) (hb : d123936 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92357, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92357, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36415 q ha hb
  have h17 (q : Pattern) (ha : d92358 q = 1) (hb : d123937 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92358, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92358, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d92359 q = 1) (hb : d123938 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92359, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92359, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92360 q = 1) (hb : d123939 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92360, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d92360, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d92361 q = 1) (hb : d123940 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92361, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92361, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92362 q = 1) (hb : d123941 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92362, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92362, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro36417 (p : Pattern) (ha : d92372 p = 1) (hb : d123951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92372 q = 1) (hb : d123951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92372, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92372, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36418 (p : Pattern) (ha : d92379 p = 1) (hb : d123958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92329 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
    | true =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d92375 q = 1) (hb : d123954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92375, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92375, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92376 q = 1) (hb : d123955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92376, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92376, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92377 q = 1) (hb : d123956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92377, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92377, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92378 q = 1) (hb : d123957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92378, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92378, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92379 q = 1) (hb : d123958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92379, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92379, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36419 (p : Pattern) (ha : d92384 p = 1) (hb : d123963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d123962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92384 q = 1) (hb : d123963 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92384, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92384, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36420 (p : Pattern) (ha : d92391 p = 1) (hb : d123970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d123968 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d123969 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92391 q = 1) (hb : d123970 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92391, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92391, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36421 (p : Pattern) (ha : d52123 p = 1) (hb : d123974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14077 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14077, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52123 q = 1) (hb : d123974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52123, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52123, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36422 (p : Pattern) (ha : d92396 p = 1) (hb : d123980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52124 q = 1) (hb : d123975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52124, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36421 q ha hb
    | true =>
      simp only [d52124, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36405 q ha hb
  have h2 (q : Pattern) (ha : d52125 q = 1) (hb : d123976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52125, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52125, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52126 q = 1) (hb : d123977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52126, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52126, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81585 q = 1) (hb : d123978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81585, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d51996 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51996, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36405 q ha hb
    | true =>
      simp only [d51996, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h6 (q : Pattern) (ha : d51997 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51997, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51997, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51998 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51998, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51998, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52222 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52222, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52222, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92395 q = 1) (hb : d123979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92395, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92395, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92396 q = 1) (hb : d123980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92396, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92396, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36423 (p : Pattern) (ha : d92402 p = 1) (hb : d123986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d123983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d123984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d123985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92402 q = 1) (hb : d123986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92402, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92402, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36424 (p : Pattern) (ha : d92408 p = 1) (hb : d123992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92405 q = 1) (hb : d123989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92405, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92405, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92406 q = 1) (hb : d123990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92406, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92406, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92407 q = 1) (hb : d123991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92407, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92407, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92408 q = 1) (hb : d123992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92408, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92408, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36425 (p : Pattern) (ha : d92414 p = 1) (hb : d123998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d123964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36419 q ha hb
    | true =>
      simp only [d92385, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d123965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d123966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d123967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d123971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36420 q ha hb
    | true =>
      simp only [d92392, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d123972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d123973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d123987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36423 q ha hb
    | true =>
      simp only [d92403, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d123988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92409 q = 1) (hb : d123993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92409, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36424 q ha hb
    | true =>
      simp only [d92409, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d123994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92410, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d123995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d123996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d123997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92414 q = 1) (hb : d123998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36426 (p : Pattern) (ha : d92415 p = 1) (hb : d123999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d123889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d123962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92415 q = 1) (hb : d123999 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92415, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92415, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36427 (p : Pattern) (ha : d92420 p = 1) (hb : d124004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d123888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d123968 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d123969 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92420 q = 1) (hb : d124004 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92420, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92420, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36428 (p : Pattern) (ha : d92424 p = 1) (hb : d124008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d123983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d123984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d123985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92424 q = 1) (hb : d124008 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92424, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92424, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36429 (p : Pattern) (ha : d92427 p = 1) (hb : d124011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d123886 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36406 q ha hb
    | true =>
      simp only [d81528, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d123887 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92405 q = 1) (hb : d123989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92405, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92405, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92406 q = 1) (hb : d123990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92406, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92406, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92407 q = 1) (hb : d123991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92407, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92407, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92427 q = 1) (hb : d124011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92427, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92427, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36430 (p : Pattern) (ha : d92433 p = 1) (hb : d124017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d123964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36419 q ha hb
    | true =>
      simp only [d92385, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d123965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d123966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d123967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d123971 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36420 q ha hb
    | true =>
      simp only [d92392, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d123972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d123973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d123987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36423 q ha hb
    | true =>
      simp only [d92403, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d123988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92409 q = 1) (hb : d123993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92409, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36424 q ha hb
    | true =>
      simp only [d92409, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d123994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92410, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d123995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d123996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d123997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92416 q = 1) (hb : d124000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92416, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36426 q ha hb
    | true =>
      simp only [d92416, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d92417 q = 1) (hb : d124001 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92417, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92417, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92418 q = 1) (hb : d124002 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92418, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92418, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92419 q = 1) (hb : d124003 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92419, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92419, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92421 q = 1) (hb : d124005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92421, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36427 q ha hb
    | true =>
      simp only [d92421, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d92422 q = 1) (hb : d124006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92422, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92422, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92423 q = 1) (hb : d124007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92423, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92423, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92425 q = 1) (hb : d124009 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36428 q ha hb
    | true =>
      simp only [d92425, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92426 q = 1) (hb : d124010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92426, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92428 q = 1) (hb : d124012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92428, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36429 q ha hb
    | true =>
      simp only [d92428, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92429 q = 1) (hb : d124013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92429, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92430 q = 1) (hb : d124014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92430, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92431 q = 1) (hb : d124015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92431, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92432 q = 1) (hb : d124016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92432, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92433 q = 1) (hb : d124017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92433, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36431 (p : Pattern) (ha : d92435 p = 1) (hb : d124019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92435 q = 1) (hb : d124019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92435, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92435, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro36432 (p : Pattern) (ha : d92442 p = 1) (hb : d124026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92425 q = 1) (hb : d124009 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36428 q ha hb
    | true =>
      simp only [d92425, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d124010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92426, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92428 q = 1) (hb : d124012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92428, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36429 q ha hb
    | true =>
      simp only [d92428, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92429 q = 1) (hb : d124013 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92429, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92430 q = 1) (hb : d124014 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92440 q = 1) (hb : d124024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92441 q = 1) (hb : d124025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92442 q = 1) (hb : d124026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36433 (p : Pattern) (ha : d52183 p = 1) (hb : d124032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14154 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14154, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52183 q = 1) (hb : d124032 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52183, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52183, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36434 (p : Pattern) (ha : d92449 p = 1) (hb : d124038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52184 q = 1) (hb : d124033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52184, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36433 q ha hb
    | true =>
      simp only [d52184, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36412 q ha hb
  have h2 (q : Pattern) (ha : d52185 q = 1) (hb : d124034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52185, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52185, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52186 q = 1) (hb : d124035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52186, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52186, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81631 q = 1) (hb : d124036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81631, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81631, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52050 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36412 q ha hb
    | true =>
      simp only [d52050, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h6 (q : Pattern) (ha : d52051 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52052 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52377 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52377, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52377, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92448 q = 1) (hb : d124037 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92448, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92448, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92449 q = 1) (hb : d124038 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92449, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92449, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36435 (p : Pattern) (ha : d92455 p = 1) (hb : d124044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36434 q ha hb
    | true =>
      simp only [d92450, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81561 q = 1) (hb : d123924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36413 q ha hb
    | true =>
      simp only [d81561, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81562 q = 1) (hb : d123925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92452 q = 1) (hb : d124041 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92452, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92452, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92453 q = 1) (hb : d124042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92453, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92453, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92454 q = 1) (hb : d124043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92454, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92454, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92455 q = 1) (hb : d124044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92455, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92455, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36436 (p : Pattern) (ha : d92461 p = 1) (hb : d124050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81561 q = 1) (hb : d123924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36413 q ha hb
    | true =>
      simp only [d81561, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81562 q = 1) (hb : d123925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92458 q = 1) (hb : d124047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92458, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92458, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92459 q = 1) (hb : d124048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92459, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92459, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92460 q = 1) (hb : d124049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92460, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92460, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92461 q = 1) (hb : d124050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92461, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92461, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36437 (p : Pattern) (ha : d92467 p = 1) (hb : d124056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92456 q = 1) (hb : d124045 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92456, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36435 q ha hb
    | true =>
      simp only [d92456, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36414 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d124046 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92457, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92462 q = 1) (hb : d124051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92462, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36436 q ha hb
    | true =>
      simp only [d92462, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92463 q = 1) (hb : d124052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92463, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92463, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92464 q = 1) (hb : d124053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92465 q = 1) (hb : d124054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92466 q = 1) (hb : d124055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92467 q = 1) (hb : d124056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36438 (p : Pattern) (ha : d92473 p = 1) (hb : d124062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92373 q = 1) (hb : d123952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92373, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92373, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36417 q ha hb
  have h2 (q : Pattern) (ha : d92374 q = 1) (hb : d123953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92374, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92374, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92380 q = 1) (hb : d123959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92380, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36417 q ha hb
    | true =>
      simp only [d92380, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36418 q ha hb
  have h4 (q : Pattern) (ha : d92381 q = 1) (hb : d123960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92381, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92381, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92382 q = 1) (hb : d123961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92382, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92382, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92434 q = 1) (hb : d124018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36425 q ha hb
    | true =>
      simp only [d92434, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36430 q ha hb
  have h7 (q : Pattern) (ha : d92436 q = 1) (hb : d124020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92436, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36431 q ha hb
    | true =>
      simp only [d92436, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d92437 q = 1) (hb : d124021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92437, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92438 q = 1) (hb : d124022 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92438, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92439 q = 1) (hb : d124023 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92439, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92443 q = 1) (hb : d124027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92443, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36432 q ha hb
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
  have h13 (q : Pattern) (ha : d92444 q = 1) (hb : d124028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92444, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92445 q = 1) (hb : d124029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92445, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92446 q = 1) (hb : d124030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92446, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92447 q = 1) (hb : d124031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92447, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92468 q = 1) (hb : d124057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92468, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36437 q ha hb
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
  have h19 (q : Pattern) (ha : d92469 q = 1) (hb : d124058 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92469, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92470 q = 1) (hb : d124059 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92470, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92471 q = 1) (hb : d124060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92471, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92472 q = 1) (hb : d124061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92472, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92473 q = 1) (hb : d124062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92473, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36439 (p : Pattern) (ha : d92479 p = 1) (hb : d124068 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d92363 q = 1) (hb : d123942 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92363, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92363, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36416 q ha hb
  have h6 (q : Pattern) (ha : d92364 q = 1) (hb : d123943 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92364, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92364, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92365 q = 1) (hb : d123944 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92365, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92365, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92366 q = 1) (hb : d123945 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92366, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92366, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92367 q = 1) (hb : d123946 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92367, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92367, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92474 q = 1) (hb : d124063 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92474, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36438 q ha hb
  have h11 (q : Pattern) (ha : d92475 q = 1) (hb : d124064 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92475, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92476 q = 1) (hb : d124065 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92476, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92477 q = 1) (hb : d124066 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92477, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92478 q = 1) (hb : d124067 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92478, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92479 q = 1) (hb : d124068 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92479, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36440 (p : Pattern) (ha : d52228 p = 1) (hb : d124070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51996 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51996, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36405 q ha hb
    | true =>
      simp only [d51996, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d51997 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51997, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51997, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51998 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51998, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51998, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52222 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52222, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52222, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52227 q = 1) (hb : d124069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52227, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52227, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52228 q = 1) (hb : d124070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52228, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52228, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36441 (p : Pattern) (ha : d52238 p = 1) (hb : d124080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52235 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52236 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52237 q = 1) (hb : d124079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52237, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52237, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52238 q = 1) (hb : d124080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52238, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52238, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36442 (p : Pattern) (ha : d52248 p = 1) (hb : d124090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52235 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52236 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52237 q = 1) (hb : d124079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52237, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52237, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52248 q = 1) (hb : d124090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52248, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52248, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36443 (p : Pattern) (ha : d52348 p = 1) (hb : d124175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52337 q = 1) (hb : d124164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52337, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
    | true =>
      simp only [d52337, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52338 q = 1) (hb : d124165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52338, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52338, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52339 q = 1) (hb : d124166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52339, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52339, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52340 q = 1) (hb : d124167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52340, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52340, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52341 q = 1) (hb : d124168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52341, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52341, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52343 q = 1) (hb : d124170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52343, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36442 q ha hb
    | true =>
      simp only [d52343, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52344 q = 1) (hb : d124171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52344, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52344, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52345 q = 1) (hb : d124172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52345, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52345, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52346 q = 1) (hb : d124173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52346, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52346, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52347 q = 1) (hb : d124174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52347, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52347, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52348 q = 1) (hb : d124175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52348, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52348, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36444 (p : Pattern) (ha : d52357 p = 1) (hb : d124184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52343 q = 1) (hb : d124170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52343, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36442 q ha hb
    | true =>
      simp only [d52343, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52344 q = 1) (hb : d124171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52344, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52344, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52345 q = 1) (hb : d124172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52345, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52345, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52346 q = 1) (hb : d124173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52346, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52346, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52347 q = 1) (hb : d124174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52347, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52347, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52357 q = 1) (hb : d124184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52357, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52357, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36445 (p : Pattern) (ha : d52387 p = 1) (hb : d124204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52050 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36412 q ha hb
    | true =>
      simp only [d52050, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d52051 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52052 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52377 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52377, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52377, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52386 q = 1) (hb : d124203 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52386, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52386, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52387 q = 1) (hb : d124204 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52387, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52387, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36446 (p : Pattern) (ha : d52398 p = 1) (hb : d124227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52388 q = 1) (hb : d124205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52388, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36445 q ha hb
    | true =>
      simp only [d52388, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52389 q = 1) (hb : d124206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52389, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52389, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52395 q = 1) (hb : d124224 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52395, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52395, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52396 q = 1) (hb : d124225 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52396, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52396, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52397 q = 1) (hb : d124226 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52397, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52397, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52398 q = 1) (hb : d124227 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52398, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52398, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36447 (p : Pattern) (ha : d52413 p = 1) (hb : d124233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52408 q = 1) (hb : d124228 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52408, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36446 q ha hb
    | true =>
      simp only [d52408, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52409 q = 1) (hb : d124229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52409, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52409, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52410 q = 1) (hb : d124230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52410, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52410, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52411 q = 1) (hb : d124231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52411, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52411, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52412 q = 1) (hb : d124232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52412, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52412, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52413 q = 1) (hb : d124233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52413, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52413, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36448 (p : Pattern) (ha : d92483 p = 1) (hb : d124076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92482 q = 1) (hb : d124075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92482, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92482, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92483 q = 1) (hb : d124076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92483, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92483, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36449 (p : Pattern) (ha : d92489 p = 1) (hb : d124086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36448 q ha hb
    | true =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92489 q = 1) (hb : d124086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92489, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92489, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36450 (p : Pattern) (ha : d92492 p = 1) (hb : d124089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92482 q = 1) (hb : d124075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92482, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92482, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92492 q = 1) (hb : d124089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92492, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92492, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36451 (p : Pattern) (ha : d92498 p = 1) (hb : d124096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36448 q ha hb
    | true =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92493 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36450 q ha hb
    | true =>
      simp only [d92493, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36442 q ha hb
  have h7 (q : Pattern) (ha : d92494 q = 1) (hb : d124092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92494, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92494, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92495 q = 1) (hb : d124093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92495, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92495, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92496 q = 1) (hb : d124094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92496, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92496, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92497 q = 1) (hb : d124095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92497, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92497, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92498 q = 1) (hb : d124096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92498, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92498, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36452 (p : Pattern) (ha : d52261 p = 1) (hb : d124103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52235 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52236 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52260 q = 1) (hb : d124102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52260, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52260, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52261 q = 1) (hb : d124103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52261, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52261, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36453 (p : Pattern) (ha : d52271 p = 1) (hb : d124113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52235 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52269 q = 1) (hb : d124111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52269, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52269, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52270 q = 1) (hb : d124112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52270, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52270, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52271 q = 1) (hb : d124113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52271, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52271, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36454 (p : Pattern) (ha : d92503 p = 1) (hb : d124101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92502 q = 1) (hb : d124100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92503 q = 1) (hb : d124101 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92503, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92503, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36455 (p : Pattern) (ha : d92510 p = 1) (hb : d124110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92508 q = 1) (hb : d124108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92509 q = 1) (hb : d124109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92509, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92510 q = 1) (hb : d124110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92510, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92510, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36456 (p : Pattern) (ha : d81587 p = 1) (hb : d123980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52124 q = 1) (hb : d123975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52124, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36421 q ha hb
    | true =>
      simp only [d52124, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36405 q ha hb
  have h2 (q : Pattern) (ha : d52125 q = 1) (hb : d123976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52125, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52125, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52126 q = 1) (hb : d123977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52126, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52126, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81585 q = 1) (hb : d123978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81585, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68915 q = 1) (hb : d123880 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34762 q ha hb
    | true =>
      simp only [d68915, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h6 (q : Pattern) (ha : d68916 q = 1) (hb : d123881 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68917 q = 1) (hb : d123882 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68918 q = 1) (hb : d123883 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d68918, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68918, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81586 q = 1) (hb : d123979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81586, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81586, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81587 q = 1) (hb : d123980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81587, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81587, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36457 (p : Pattern) (ha : d52295 p = 1) (hb : d124117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14261 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14261, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14261, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52295 q = 1) (hb : d124117 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52295, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52295, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36458 (p : Pattern) (ha : d92516 p = 1) (hb : d124123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52296 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52296, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36457 q ha hb
    | true =>
      simp only [d52296, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36421 q ha hb
  have h2 (q : Pattern) (ha : d52297 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52297, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52297, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52298 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52298, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52298, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92514 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92514, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92514, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52124 q = 1) (hb : d123975 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52124, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36421 q ha hb
    | true =>
      simp only [d52124, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36405 q ha hb
  have h6 (q : Pattern) (ha : d52125 q = 1) (hb : d123976 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52125, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52125, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52126 q = 1) (hb : d123977 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52126, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52126, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81585 q = 1) (hb : d123978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81585, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92515 q = 1) (hb : d124122 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92515, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92515, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92516 q = 1) (hb : d124123 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92516, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92516, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36459 (p : Pattern) (ha : d92522 p = 1) (hb : d124129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92517 q = 1) (hb : d124124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92517, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36458 q ha hb
    | true =>
      simp only [d92517, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92518 q = 1) (hb : d124125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92518, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92518, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81588 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36456 q ha hb
    | true =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81589 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92519 q = 1) (hb : d124126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92519, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92520 q = 1) (hb : d124127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92520, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92521 q = 1) (hb : d124128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92521, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92522 q = 1) (hb : d124129 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92522, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92522, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36460 (p : Pattern) (ha : d92526 p = 1) (hb : d124076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81588 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36456 q ha hb
    | true =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81589 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92523 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92523, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92524 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92524, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92525 q = 1) (hb : d124075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92525, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92526 q = 1) (hb : d124076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92526, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92526, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36461 (p : Pattern) (ha : d92532 p = 1) (hb : d124135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92529 q = 1) (hb : d124132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92529, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92529, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92530 q = 1) (hb : d124133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92530, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92530, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92531 q = 1) (hb : d124134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92531, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92531, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92532 q = 1) (hb : d124135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92532, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92532, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36462 (p : Pattern) (ha : d92538 p = 1) (hb : d124141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d124104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36454 q ha hb
    | true =>
      simp only [d92504, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36452 q ha hb
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d124105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d124106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d124107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d124114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36455 q ha hb
    | true =>
      simp only [d92511, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36453 q ha hb
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d124115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d124116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d124130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36459 q ha hb
    | true =>
      simp only [d92527, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36460 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d124131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92533 q = 1) (hb : d124136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92533, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36461 q ha hb
    | true =>
      simp only [d92533, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92534 q = 1) (hb : d124137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92534, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92534, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d124138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d124139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d124140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92538 q = 1) (hb : d124141 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36463 (p : Pattern) (ha : d52317 p = 1) (hb : d124143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52235 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52236 q = 1) (hb : d124078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52236, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52260 q = 1) (hb : d124102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52260, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52260, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52317 q = 1) (hb : d124143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52317, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52317, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36464 (p : Pattern) (ha : d52323 p = 1) (hb : d124149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52235 q = 1) (hb : d124077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52235, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52269 q = 1) (hb : d124111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52269, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52269, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52270 q = 1) (hb : d124112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52270, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52270, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52323 q = 1) (hb : d124149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52323, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52323, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36465 (p : Pattern) (ha : d92539 p = 1) (hb : d124142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92502 q = 1) (hb : d124100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92539 q = 1) (hb : d124142 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92539, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92539, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36466 (p : Pattern) (ha : d92544 p = 1) (hb : d124148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92508 q = 1) (hb : d124108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92509 q = 1) (hb : d124109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92509, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92544 q = 1) (hb : d124148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92544, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92544, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36467 (p : Pattern) (ha : d92548 p = 1) (hb : d124153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92517 q = 1) (hb : d124124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92517, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36458 q ha hb
    | true =>
      simp only [d92517, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92518 q = 1) (hb : d124125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92518, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92518, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81588 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36456 q ha hb
    | true =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81589 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92519 q = 1) (hb : d124126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92519, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92520 q = 1) (hb : d124127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92520, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92521 q = 1) (hb : d124128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92521, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92548 q = 1) (hb : d124153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92548, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92548, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36468 (p : Pattern) (ha : d92549 p = 1) (hb : d124089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81588 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36456 q ha hb
    | true =>
      simp only [d81588, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81589 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52229 q = 1) (hb : d124071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36440 q ha hb
    | true =>
      simp only [d52229, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d124072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52230, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92523 q = 1) (hb : d124073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92523, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92524 q = 1) (hb : d124074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92524, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92525 q = 1) (hb : d124075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92525, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92549 q = 1) (hb : d124089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92549, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92549, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36469 (p : Pattern) (ha : d92552 p = 1) (hb : d124156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d123981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36422 q ha hb
    | true =>
      simp only [d92397, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d123982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92529 q = 1) (hb : d124132 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92529, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92529, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92530 q = 1) (hb : d124133 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92530, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92530, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92531 q = 1) (hb : d124134 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92531, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92531, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92552 q = 1) (hb : d124156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92552, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92552, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36470 (p : Pattern) (ha : d92558 p = 1) (hb : d124162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d124104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36454 q ha hb
    | true =>
      simp only [d92504, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36452 q ha hb
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d124105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d124106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d124107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d124114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36455 q ha hb
    | true =>
      simp only [d92511, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36453 q ha hb
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d124115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d124116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d124130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36459 q ha hb
    | true =>
      simp only [d92527, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36460 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d124131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92533 q = 1) (hb : d124136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92533, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36461 q ha hb
    | true =>
      simp only [d92533, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92534 q = 1) (hb : d124137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92534, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92534, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d124138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d124139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d124140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92540 q = 1) (hb : d124144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92540, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36465 q ha hb
    | true =>
      simp only [d92540, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36463 q ha hb
  have h17 (q : Pattern) (ha : d92541 q = 1) (hb : d124145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92541, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92541, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92542 q = 1) (hb : d124146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92542, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92542, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92543 q = 1) (hb : d124147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92543, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92543, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92545 q = 1) (hb : d124150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92545, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36466 q ha hb
    | true =>
      simp only [d92545, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36464 q ha hb
  have h21 (q : Pattern) (ha : d92546 q = 1) (hb : d124151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92546, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92546, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92547 q = 1) (hb : d124152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92547, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92547, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92550 q = 1) (hb : d124154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36467 q ha hb
    | true =>
      simp only [d92550, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36468 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92551 q = 1) (hb : d124155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92551, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92553 q = 1) (hb : d124157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92553, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36469 q ha hb
    | true =>
      simp only [d92553, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92554 q = 1) (hb : d124158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92554, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92554, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92555 q = 1) (hb : d124159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92555, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92556 q = 1) (hb : d124160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92556, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92557 q = 1) (hb : d124161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92557, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92558 q = 1) (hb : d124162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92558, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36471 (p : Pattern) (ha : d92565 p = 1) (hb : d124169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92560 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92560, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36460 q ha hb
    | true =>
      simp only [d92560, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
  have h2 (q : Pattern) (ha : d92561 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92561, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92561, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92562 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92562, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92562, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92563 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92563, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92563, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92564 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92564, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92564, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52337 q = 1) (hb : d124164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52337, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
    | true =>
      simp only [d52337, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52338 q = 1) (hb : d124165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52338, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52338, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52339 q = 1) (hb : d124166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52339, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52339, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52340 q = 1) (hb : d124167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52340, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52340, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52341 q = 1) (hb : d124168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52341, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52341, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92565 q = 1) (hb : d124169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92565, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92565, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36472 (p : Pattern) (ha : d92572 p = 1) (hb : d124182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92550 q = 1) (hb : d124154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36467 q ha hb
    | true =>
      simp only [d92550, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36468 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d124155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92551, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92553 q = 1) (hb : d124157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92553, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36469 q ha hb
    | true =>
      simp only [d92553, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92554 q = 1) (hb : d124158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92554, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92554, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92555 q = 1) (hb : d124159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92570 q = 1) (hb : d124180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92571 q = 1) (hb : d124181 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92572 q = 1) (hb : d124182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36473 (p : Pattern) (ha : d81633 p = 1) (hb : d124038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52184 q = 1) (hb : d124033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52184, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36433 q ha hb
    | true =>
      simp only [d52184, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36412 q ha hb
  have h2 (q : Pattern) (ha : d52185 q = 1) (hb : d124034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52185, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52185, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52186 q = 1) (hb : d124035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52186, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52186, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81631 q = 1) (hb : d124036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81631, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81631, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75841 q = 1) (hb : d123918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34769 q ha hb
    | true =>
      simp only [d75841, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h6 (q : Pattern) (ha : d75842 q = 1) (hb : d123919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75843 q = 1) (hb : d123920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75844 q = 1) (hb : d123921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75844, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75844, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81632 q = 1) (hb : d124037 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81632, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81632, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81633 q = 1) (hb : d124038 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81633, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81633, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36474 (p : Pattern) (ha : d52368 p = 1) (hb : d124190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14370 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14370, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14370, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52368 q = 1) (hb : d124190 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52368, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52368, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36475 (p : Pattern) (ha : d92580 p = 1) (hb : d124196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52369 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52369, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36474 q ha hb
    | true =>
      simp only [d52369, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36433 q ha hb
  have h2 (q : Pattern) (ha : d52370 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52370, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52370, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52371 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52371, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52371, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92578 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92578, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92578, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52184 q = 1) (hb : d124033 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52184, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36433 q ha hb
    | true =>
      simp only [d52184, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36412 q ha hb
  have h6 (q : Pattern) (ha : d52185 q = 1) (hb : d124034 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52185, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52185, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52186 q = 1) (hb : d124035 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52186, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52186, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81631 q = 1) (hb : d124036 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81631, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81631, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92579 q = 1) (hb : d124195 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92579, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92579, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92580 q = 1) (hb : d124196 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92580, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92580, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36476 (p : Pattern) (ha : d92586 p = 1) (hb : d124202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92581 q = 1) (hb : d124197 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92581, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36475 q ha hb
    | true =>
      simp only [d92581, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92582 q = 1) (hb : d124198 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92582, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92582, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81634 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81634, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36473 q ha hb
    | true =>
      simp only [d81634, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81635 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81635, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81635, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92583 q = 1) (hb : d124199 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92583, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92583, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92584 q = 1) (hb : d124200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92584, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92584, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92585 q = 1) (hb : d124201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92585, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92585, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92586 q = 1) (hb : d124202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92586, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92586, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36477 (p : Pattern) (ha : d92590 p = 1) (hb : d124210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81634 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81634, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36473 q ha hb
    | true =>
      simp only [d81634, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81635 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81635, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81635, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52388 q = 1) (hb : d124205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52388, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36445 q ha hb
    | true =>
      simp only [d52388, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52389 q = 1) (hb : d124206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52389, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52389, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92587 q = 1) (hb : d124207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92587, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92587, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92588 q = 1) (hb : d124208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92588, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92588, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92589 q = 1) (hb : d124209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92589, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92589, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92590 q = 1) (hb : d124210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92590, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92590, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36478 (p : Pattern) (ha : d92601 p = 1) (hb : d124216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36434 q ha hb
    | true =>
      simp only [d92450, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92598 q = 1) (hb : d124213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92598, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92598, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92599 q = 1) (hb : d124214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92599, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92599, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92600 q = 1) (hb : d124215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92600, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92600, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92601 q = 1) (hb : d124216 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92601, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92601, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36479 (p : Pattern) (ha : d92607 p = 1) (hb : d124222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92591 q = 1) (hb : d124211 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92591, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36476 q ha hb
    | true =>
      simp only [d92591, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36477 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d124212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92597, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92602 q = 1) (hb : d124217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92602, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36478 q ha hb
    | true =>
      simp only [d92602, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92603 q = 1) (hb : d124218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92603, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92603, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92604 q = 1) (hb : d124219 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92605 q = 1) (hb : d124220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92606 q = 1) (hb : d124221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92607 q = 1) (hb : d124222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36480 (p : Pattern) (ha : d92613 p = 1) (hb : d124239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92490 q = 1) (hb : d124087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92490, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92490, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36449 q ha hb
  have h2 (q : Pattern) (ha : d92491 q = 1) (hb : d124088 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92491, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92491, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92499 q = 1) (hb : d124097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92499, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36449 q ha hb
    | true =>
      simp only [d92499, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36451 q ha hb
  have h4 (q : Pattern) (ha : d92500 q = 1) (hb : d124098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92500, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92500, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92501 q = 1) (hb : d124099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92501, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92501, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92559 q = 1) (hb : d124163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36462 q ha hb
    | true =>
      simp only [d92559, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36470 q ha hb
  have h7 (q : Pattern) (ha : d92566 q = 1) (hb : d124176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92566, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36471 q ha hb
    | true =>
      simp only [d92566, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36443 q ha hb
  have h8 (q : Pattern) (ha : d92567 q = 1) (hb : d124177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92567, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92568 q = 1) (hb : d124178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92568, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92569 q = 1) (hb : d124179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92569, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92573 q = 1) (hb : d124183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92573, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36472 q ha hb
  have h12 (q : Pattern) (ha : d52358 q = 1) (hb : d124185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52358, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52358, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36444 q ha hb
  have h13 (q : Pattern) (ha : d92574 q = 1) (hb : d124186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92574, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92575 q = 1) (hb : d124187 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92575, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92576 q = 1) (hb : d124188 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92576, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92577 q = 1) (hb : d124189 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92577, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92608 q = 1) (hb : d124223 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92608, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36479 q ha hb
  have h18 (q : Pattern) (ha : d52414 q = 1) (hb : d124234 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52414, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52414, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36447 q ha hb
  have h19 (q : Pattern) (ha : d92609 q = 1) (hb : d124235 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92609, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92610 q = 1) (hb : d124236 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92610, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92611 q = 1) (hb : d124237 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92611, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92612 q = 1) (hb : d124238 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92612, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92613 q = 1) (hb : d124239 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92613, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36481 (p : Pattern) (ha : d92619 p = 1) (hb : d124245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d124240 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36480 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d124241 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d124242 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d124243 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d124244 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d124245 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36482 (p : Pattern) (ha : d52435 p = 1) (hb : d123974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14077 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14077, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52435 q = 1) (hb : d123974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52435, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52435, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36483 (p : Pattern) (ha : d52450 p = 1) (hb : d124256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52440 q = 1) (hb : d124247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52440, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36482 q ha hb
    | true =>
      simp only [d52440, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h2 (q : Pattern) (ha : d52441 q = 1) (hb : d124248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52441, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52441, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52442 q = 1) (hb : d124249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52442, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52442, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52444 q = 1) (hb : d124250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52444, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52444, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52449 q = 1) (hb : d124255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52449, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52449, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52450 q = 1) (hb : d124256 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52450, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52450, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36484 (p : Pattern) (ha : d52460 p = 1) (hb : d124266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52457 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52458 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52459 q = 1) (hb : d124265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52459, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52459, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52460 q = 1) (hb : d124266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52460, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52460, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36485 (p : Pattern) (ha : d52470 p = 1) (hb : d124276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52457 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52458 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52459 q = 1) (hb : d124265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52459, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52459, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52470 q = 1) (hb : d124276 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52470, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52470, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36486 (p : Pattern) (ha : d52569 p = 1) (hb : d124361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52558 q = 1) (hb : d124350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52558, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
    | true =>
      simp only [d52558, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52559 q = 1) (hb : d124351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52559, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52559, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52560 q = 1) (hb : d124352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52560, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52560, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52561 q = 1) (hb : d124353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52561, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52561, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52562 q = 1) (hb : d124354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52562, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52562, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52564 q = 1) (hb : d124356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52564, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36485 q ha hb
    | true =>
      simp only [d52564, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52565 q = 1) (hb : d124357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52565, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52565, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52566 q = 1) (hb : d124358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52566, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52566, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52567 q = 1) (hb : d124359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52567, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52567, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52568 q = 1) (hb : d124360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52568, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52568, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52569 q = 1) (hb : d124361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52569, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52569, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36487 (p : Pattern) (ha : d52578 p = 1) (hb : d124370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52564 q = 1) (hb : d124356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52564, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36485 q ha hb
    | true =>
      simp only [d52564, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52565 q = 1) (hb : d124357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52565, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52565, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52566 q = 1) (hb : d124358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52566, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52566, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52567 q = 1) (hb : d124359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52567, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52567, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52568 q = 1) (hb : d124360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52568, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52568, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52578 q = 1) (hb : d124370 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52578, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52578, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36488 (p : Pattern) (ha : d52600 p = 1) (hb : d124032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14154 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14154, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52600 q = 1) (hb : d124032 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52600, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52600, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36489 (p : Pattern) (ha : d52624 p = 1) (hb : d124398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52606 q = 1) (hb : d124385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52606, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36488 q ha hb
    | true =>
      simp only [d52606, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h2 (q : Pattern) (ha : d52607 q = 1) (hb : d124386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52607, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52607, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52608 q = 1) (hb : d124387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52608, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52608, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52614 q = 1) (hb : d124388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52614, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52614, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52623 q = 1) (hb : d124397 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52623, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52623, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52624 q = 1) (hb : d124398 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52624, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52624, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36490 (p : Pattern) (ha : d52635 p = 1) (hb : d124421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52625 q = 1) (hb : d124399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52625, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36489 q ha hb
    | true =>
      simp only [d52625, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52626 q = 1) (hb : d124400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52626, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52626, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52632 q = 1) (hb : d124418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52632, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52632, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52633 q = 1) (hb : d124419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52633, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52633, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52634 q = 1) (hb : d124420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52634, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52634, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52635 q = 1) (hb : d124421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52635, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52635, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36491 (p : Pattern) (ha : d52650 p = 1) (hb : d124427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52645 q = 1) (hb : d124422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52645, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36490 q ha hb
    | true =>
      simp only [d52645, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52646 q = 1) (hb : d124423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52646, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52646, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52647 q = 1) (hb : d124424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52647, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52647, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52648 q = 1) (hb : d124425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52648, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52648, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52649 q = 1) (hb : d124426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52649, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52649, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52650 q = 1) (hb : d124427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52650, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52650, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36492 (p : Pattern) (ha : d52433 p = 1) (hb : d124117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14261 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14261, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14261, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52433 q = 1) (hb : d124117 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52433, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52433, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36493 (p : Pattern) (ha : d92622 p = 1) (hb : d124252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52436 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52436, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36492 q ha hb
    | true =>
      simp only [d52436, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36482 q ha hb
  have h2 (q : Pattern) (ha : d52437 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52437, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52437, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52438 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52438, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52438, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81663 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81663, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81663, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52440 q = 1) (hb : d124247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52440, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36482 q ha hb
    | true =>
      simp only [d52440, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h6 (q : Pattern) (ha : d52441 q = 1) (hb : d124248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52441, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52441, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52442 q = 1) (hb : d124249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52442, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52442, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52444 q = 1) (hb : d124250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52444, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52444, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92621 q = 1) (hb : d124251 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92621, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92621, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92622 q = 1) (hb : d124252 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92622, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92622, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36494 (p : Pattern) (ha : d92628 p = 1) (hb : d124262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92627 q = 1) (hb : d124261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92627, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92627, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92628 q = 1) (hb : d124262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92628, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92628, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36495 (p : Pattern) (ha : d92634 p = 1) (hb : d124272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92629 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36494 q ha hb
    | true =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
  have h2 (q : Pattern) (ha : d92630 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92630, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92630, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92631 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92631, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92631, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92632 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92632, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92632, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92633 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92633, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92633, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92634 q = 1) (hb : d124272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92634, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92634, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36496 (p : Pattern) (ha : d92637 p = 1) (hb : d124275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92627 q = 1) (hb : d124261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92627, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92627, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92637 q = 1) (hb : d124275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92637, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92637, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36497 (p : Pattern) (ha : d92643 p = 1) (hb : d124282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92629 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36494 q ha hb
    | true =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
  have h2 (q : Pattern) (ha : d92630 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92630, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92630, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92631 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92631, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92631, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92632 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92632, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92632, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92633 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92633, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92633, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92638 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36496 q ha hb
    | true =>
      simp only [d92638, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36485 q ha hb
  have h7 (q : Pattern) (ha : d92639 q = 1) (hb : d124278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92639, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92639, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92640 q = 1) (hb : d124279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92640, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92640, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92641 q = 1) (hb : d124280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92641, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92641, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92642 q = 1) (hb : d124281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92642, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92642, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92643 q = 1) (hb : d124282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92643, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92643, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36498 (p : Pattern) (ha : d52483 p = 1) (hb : d124289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52457 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52458 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52482 q = 1) (hb : d124288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52482, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52482, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52483 q = 1) (hb : d124289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52483, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52483, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36499 (p : Pattern) (ha : d52493 p = 1) (hb : d124299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52457 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52491 q = 1) (hb : d124297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52491, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52491, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52492 q = 1) (hb : d124298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52492, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52492, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52493 q = 1) (hb : d124299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52493, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52493, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
