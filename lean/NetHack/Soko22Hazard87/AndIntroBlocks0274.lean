import NetHack.Soko22Hazard87.AndIntroBlocks0273
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro68500 (p : Pattern) (ha : d269337 p = 1) (hb : d270402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d270378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68495 q ha hb
    | true =>
      simp only [d269313, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d270379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d270380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d270392 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
    | true =>
      simp only [d269327, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68498 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d270393 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d270394 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d270395 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269335 q = 1) (hb : d270400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269335, d270400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269335, d270400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269336 q = 1) (hb : d270401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269336, d270401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269336, d270401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269337 q = 1) (hb : d270402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269337, d270402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269337, d270402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro68501 (p : Pattern) (ha : d269343 p = 1) (hb : d270408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269333 q = 1) (hb : d270398 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269333, d270398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68499 q ha hb
    | true =>
      simp only [d269333, d270398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269334 q = 1) (hb : d270399 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269334, d270399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269334, d270399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269338 q = 1) (hb : d270403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269338, d270403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68500 q ha hb
    | true =>
      simp only [d269338, d270403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269339 q = 1) (hb : d270404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269339, d270404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269339, d270404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269340 q = 1) (hb : d270405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269340, d270405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269340, d270405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269341 q = 1) (hb : d270406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269341, d270406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269341, d270406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269342 q = 1) (hb : d270407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269342, d270407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269342, d270407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269343 q = 1) (hb : d270408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269343, d270408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269343, d270408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68502 (p : Pattern) (ha : d269345 p = 1) (hb : d270410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269307 q = 1) (hb : d270372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d270372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d270372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68448 q ha hb
  have h2 (q : Pattern) (ha : d269031 q = 1) (hb : d270141 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d270141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68448 q ha hb
    | true =>
      simp only [d269031, d270141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269308 q = 1) (hb : d270373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d270373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269308, d270373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269032 q = 1) (hb : d270142 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d270142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269032, d270142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269309 q = 1) (hb : d270374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d270374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269309, d270374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269310 q = 1) (hb : d270375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d270375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269310, d270375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269344 q = 1) (hb : d270409 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269344, d270409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269344, d270409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269321 q = 1) (hb : d270386 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269321, d270386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269321, d270386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68451 q ha hb
  have h9 (q : Pattern) (ha : d269054 q = 1) (hb : d270161 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269054, d270161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68451 q ha hb
    | true =>
      simp only [d269054, d270161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269322 q = 1) (hb : d270387 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269322, d270387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269322, d270387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269055 q = 1) (hb : d270162 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269055, d270162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269055, d270162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269323 q = 1) (hb : d270388 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269323, d270388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269323, d270388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269324 q = 1) (hb : d270389 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269324, d270389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269324, d270389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269325 q = 1) (hb : d270390 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269325, d270390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269325, d270390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269345 q = 1) (hb : d270410 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269345, d270410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269345, d270410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68503 (p : Pattern) (ha : d269351 p = 1) (hb : d270416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269346 q = 1) (hb : d270411 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269346, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
    | true =>
      simp only [d269346, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68502 q ha hb
  have h2 (q : Pattern) (ha : d269347 q = 1) (hb : d270412 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269347, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269347, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269348 q = 1) (hb : d270413 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269348, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269348, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269349 q = 1) (hb : d270414 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269349, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269349, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269350 q = 1) (hb : d270415 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269350, d270415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269350, d270415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269351 q = 1) (hb : d270416 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269351, d270416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269351, d270416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68504 (p : Pattern) (ha : d269357 p = 1) (hb : d270422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269338 q = 1) (hb : d270403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269338, d270403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68500 q ha hb
    | true =>
      simp only [d269338, d270403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269339 q = 1) (hb : d270404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269339, d270404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269339, d270404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269352 q = 1) (hb : d270417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68503 q ha hb
    | true =>
      simp only [d269352, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269353 q = 1) (hb : d270418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269354 q = 1) (hb : d270419 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269354, d270419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269354, d270419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269355 q = 1) (hb : d270420 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269355, d270420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269355, d270420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269356 q = 1) (hb : d270421 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269356, d270421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269356, d270421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269357 q = 1) (hb : d270422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269357, d270422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269357, d270422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68505 (p : Pattern) (ha : d269378 p = 1) (hb : d270377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269303 q = 1) (hb : d270368 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269303, d270368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269303, d270368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68447 q ha hb
  have h2 (q : Pattern) (ha : d269026 q = 1) (hb : d270136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269026, d270136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68447 q ha hb
    | true =>
      simp only [d269026, d270136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269304 q = 1) (hb : d270369 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269304, d270369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269304, d270369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269027 q = 1) (hb : d270137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269027, d270137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269027, d270137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269305 q = 1) (hb : d270370 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269305, d270370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269305, d270370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269306 q = 1) (hb : d270371 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269306, d270371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269306, d270371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269307 q = 1) (hb : d270372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269307, d270372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269307, d270372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68448 q ha hb
  have h8 (q : Pattern) (ha : d269031 q = 1) (hb : d270141 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269031, d270141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68448 q ha hb
    | true =>
      simp only [d269031, d270141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269308 q = 1) (hb : d270373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269308, d270373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269308, d270373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269032 q = 1) (hb : d270142 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269032, d270142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269032, d270142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269309 q = 1) (hb : d270374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269309, d270374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269309, d270374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269310 q = 1) (hb : d270375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269310, d270375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269310, d270375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269311 q = 1) (hb : d270376 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269311, d270376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269311, d270376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269373 q = 1) (hb : d270348 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269373, d270348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269373, d270348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68475 q ha hb
  have h15 (q : Pattern) (ha : d269174 q = 1) (hb : d270126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269174, d270126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68475 q ha hb
    | true =>
      simp only [d269174, d270126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269374 q = 1) (hb : d270349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269374, d270349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269374, d270349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269175 q = 1) (hb : d270127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269175, d270127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269175, d270127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269375 q = 1) (hb : d270350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269375, d270350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269375, d270350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269376 q = 1) (hb : d270351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269376, d270351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269376, d270351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269377 q = 1) (hb : d270362 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269377, d270362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269377, d270362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269378 q = 1) (hb : d270377 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269378, d270377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269378, d270377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro68506 (p : Pattern) (ha : d269384 p = 1) (hb : d270425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269379 q = 1) (hb : d270372 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269379, d270372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269379, d270372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68477 q ha hb
  have h2 (q : Pattern) (ha : d269181 q = 1) (hb : d270141 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269181, d270141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68477 q ha hb
    | true =>
      simp only [d269181, d270141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269380 q = 1) (hb : d270373 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269380, d270373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269380, d270373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269182 q = 1) (hb : d270142 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269182, d270142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269182, d270142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269381 q = 1) (hb : d270374 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269381, d270374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269381, d270374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269382 q = 1) (hb : d270375 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269382, d270375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269382, d270375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269383 q = 1) (hb : d270409 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269383, d270409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269383, d270409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269384 q = 1) (hb : d270425 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269384, d270425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269384, d270425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68507 (p : Pattern) (ha : d269390 p = 1) (hb : d270431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d270378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68495 q ha hb
    | true =>
      simp only [d269313, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d270379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d270380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d270392 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
    | true =>
      simp only [d269327, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68498 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d270393 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d270394 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d270395 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269385 q = 1) (hb : d270426 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269385, d270426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68505 q ha hb
    | true =>
      simp only [d269385, d270426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68506 q ha hb
  have h9 (q : Pattern) (ha : d269386 q = 1) (hb : d270427 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269386, d270427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269386, d270427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269387 q = 1) (hb : d270428 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269387, d270428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269387, d270428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269388 q = 1) (hb : d270429 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269388, d270429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269388, d270429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269389 q = 1) (hb : d270430 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269389, d270430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269389, d270430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269390 q = 1) (hb : d270431 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269390, d270431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269390, d270431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro68508 (p : Pattern) (ha : d269396 p = 1) (hb : d270437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269391 q = 1) (hb : d270432 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269391, d270432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68507 q ha hb
    | true =>
      simp only [d269391, d270432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269392 q = 1) (hb : d270433 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269392, d270433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269392, d270433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269393 q = 1) (hb : d270434 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269393, d270434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269393, d270434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269394 q = 1) (hb : d270435 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269394, d270435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269394, d270435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269395 q = 1) (hb : d270436 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269395, d270436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269395, d270436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269396 q = 1) (hb : d270437 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269396, d270437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269396, d270437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68509 (p : Pattern) (ha : d269402 p = 1) (hb : d270443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269358 q = 1) (hb : d270423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269358, d270423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68501 q ha hb
    | true =>
      simp only [d269358, d270423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68504 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269372 q = 1) (hb : d270424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269372, d270424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269372, d270424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269397 q = 1) (hb : d270438 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269397, d270438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68508 q ha hb
    | true =>
      simp only [d269397, d270438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269398 q = 1) (hb : d270439 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269398, d270439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269398, d270439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269399 q = 1) (hb : d270440 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269399, d270440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269399, d270440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269400 q = 1) (hb : d270441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269400, d270441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269400, d270441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269401 q = 1) (hb : d270442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269401, d270442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269401, d270442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269402 q = 1) (hb : d270443 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269402, d270443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269402, d270443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro68510 (p : Pattern) (ha : d269370 p = 1) (hb : d270448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269352 q = 1) (hb : d270417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68503 q ha hb
    | true =>
      simp only [d269352, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269353 q = 1) (hb : d270418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269367 q = 1) (hb : d270445 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269367, d270445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269367, d270445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269368 q = 1) (hb : d270446 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269368, d270446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269368, d270446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269369 q = 1) (hb : d270447 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269369, d270447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269369, d270447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269370 q = 1) (hb : d270448 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269370, d270448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269370, d270448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68511 (p : Pattern) (ha : d269409 p = 1) (hb : d270454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269404 q = 1) (hb : d270449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269404, d270449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68510 q ha hb
    | true =>
      simp only [d269404, d270449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269405 q = 1) (hb : d270450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269405, d270450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269405, d270450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269406 q = 1) (hb : d270451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269406, d270451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269406, d270451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269407 q = 1) (hb : d270452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269407, d270452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269407, d270452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269408 q = 1) (hb : d270453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269408, d270453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269408, d270453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269409 q = 1) (hb : d270454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269409, d270454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269409, d270454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68512 (p : Pattern) (ha : d269415 p = 1) (hb : d270460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269092 q = 1) (hb : d270199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269092, d270199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269092, d270199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68458 q ha hb
  have h2 (q : Pattern) (ha : d269093 q = 1) (hb : d270200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269093, d270200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269093, d270200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269102 q = 1) (hb : d270209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269102, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68458 q ha hb
    | true =>
      simp only [d269102, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68461 q ha hb
  have h4 (q : Pattern) (ha : d269103 q = 1) (hb : d270210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269103, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269103, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269104 q = 1) (hb : d270211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269104, d270211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269104, d270211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269227 q = 1) (hb : d270305 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269227, d270305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68481 q ha hb
    | true =>
      simp only [d269227, d270305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68489 q ha hb
  have h7 (q : Pattern) (ha : d269245 q = 1) (hb : d270323 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269245, d270323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68490 q ha hb
    | true =>
      simp only [d269245, d270323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68491 q ha hb
  have h8 (q : Pattern) (ha : d269246 q = 1) (hb : d270324 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269246, d270324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269246, d270324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269247 q = 1) (hb : d270325 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269247, d270325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269247, d270325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269248 q = 1) (hb : d270326 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269248, d270326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269248, d270326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269252 q = 1) (hb : d270330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269252, d270330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269252, d270330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68492 q ha hb
  have h12 (q : Pattern) (ha : d269254 q = 1) (hb : d270332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269254, d270332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269254, d270332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68493 q ha hb
  have h13 (q : Pattern) (ha : d269255 q = 1) (hb : d270333 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269255, d270333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269255, d270333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269256 q = 1) (hb : d270334 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269256, d270334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269256, d270334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269257 q = 1) (hb : d270335 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269257, d270335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269257, d270335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269258 q = 1) (hb : d270336 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269258, d270336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269258, d270336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269403 q = 1) (hb : d270444 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269403, d270444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269403, d270444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68509 q ha hb
  have h18 (q : Pattern) (ha : d269410 q = 1) (hb : d270455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269410, d270455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269410, d270455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68511 q ha hb
  have h19 (q : Pattern) (ha : d269411 q = 1) (hb : d270456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269411, d270456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269411, d270456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269412 q = 1) (hb : d270457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269412, d270457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269412, d270457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269413 q = 1) (hb : d270458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269413, d270458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269413, d270458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269414 q = 1) (hb : d270459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269414, d270459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269414, d270459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269415 q = 1) (hb : d270460 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269415, d270460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269415, d270460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro68513 (p : Pattern) (ha : d269421 p = 1) (hb : d270466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269416 q = 1) (hb : d270461 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269416, d270461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269416, d270461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68512 q ha hb
  have h2 (q : Pattern) (ha : d269417 q = 1) (hb : d270462 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269417, d270462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269417, d270462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269418 q = 1) (hb : d270463 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269418, d270463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269418, d270463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269419 q = 1) (hb : d270464 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269419, d270464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269419, d270464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269420 q = 1) (hb : d270465 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269420, d270465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269420, d270465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269421 q = 1) (hb : d270466 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269421, d270466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269421, d270466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68514 (p : Pattern) (ha : d38156 p = 1) (hb : d269427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2013 q = 1) (hb : d53292 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38155 q = 1) (hb : d269426 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d38155, d269426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38155, d269426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38156 q = 1) (hb : d269427 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d38156, d269427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38156, d269427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68515 (p : Pattern) (ha : d38162 p = 1) (hb : d269433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269429 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38158, d269429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38159 q = 1) (hb : d269430 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38159, d269430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38159, d269430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2031 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38160 q = 1) (hb : d269431 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38160, d269431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38160, d269431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38161 q = 1) (hb : d269432 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38161, d269432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38161, d269432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d38162 q = 1) (hb : d269433 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38162, d269433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38162, d269433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro68516 (p : Pattern) (ha : d269442 p = 1) (hb : d270471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269429 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38158, d269429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38159 q = 1) (hb : d269430 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38159, d269430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38159, d269430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2031 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38160 q = 1) (hb : d269431 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38160, d269431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38160, d269431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38161 q = 1) (hb : d269432 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38161, d269432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38161, d269432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269442 q = 1) (hb : d270471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269442, d270471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269442, d270471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro68517 (p : Pattern) (ha : d269463 p = 1) (hb : d270480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269454 q = 1) (hb : d270477 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269454, d270477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269454, d270477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d269455 q = 1) (hb : d270478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269455, d270478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269455, d270478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d269456 q = 1) (hb : d270479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269456, d270479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269456, d270479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5239 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d5243 q = 1) (hb : d269458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5243, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2048 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2061 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d5244 q = 1) (hb : d269461 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5244, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5245 q = 1) (hb : d269462 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5245, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d269463 q = 1) (hb : d270480 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269463, d270480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269463, d270480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  exact h18 p ha hb
theorem andIntro68518 (p : Pattern) (ha : d269469 p = 1) (hb : d270486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38163 q = 1) (hb : d269434 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38163, d269434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68515 q ha hb
    | true =>
      simp only [d38163, d269434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38164 q = 1) (hb : d269435 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38164, d269435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38164, d269435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38165 q = 1) (hb : d269436 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38165, d269436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38165, d269436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38166 q = 1) (hb : d269437 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38166, d269437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38166, d269437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269443 q = 1) (hb : d270472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269443, d270472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68516 q ha hb
    | true =>
      simp only [d269443, d270472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269444 q = 1) (hb : d270473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269444, d270473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269444, d270473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269445 q = 1) (hb : d270474 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269445, d270474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269445, d270474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269446 q = 1) (hb : d270475 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269446, d270475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269446, d270475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269447 q = 1) (hb : d270476 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269447, d270476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269447, d270476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269452 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d269464 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
    | true =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269465 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269466 q = 1) (hb : d270483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269466, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269466, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269467 q = 1) (hb : d270484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269467, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269467, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269468 q = 1) (hb : d270485 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269468, d270485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269468, d270485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269469 q = 1) (hb : d270486 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269469, d270486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269469, d270486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro68519 (p : Pattern) (ha : d38199 p = 1) (hb : d269470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2013 q = 1) (hb : d53292 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38155 q = 1) (hb : d269426 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d38155, d269426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38155, d269426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2027 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38199 q = 1) (hb : d269470 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d38199, d269470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38199, d269470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro68520 (p : Pattern) (ha : d269476 p = 1) (hb : d270490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269429 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38158, d269429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38159 q = 1) (hb : d269430 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38159, d269430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38159, d269430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2031 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38160 q = 1) (hb : d269431 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38160, d269431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38160, d269431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38161 q = 1) (hb : d269432 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38161, d269432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38161, d269432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d38158 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38200 q = 1) (hb : d269471 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38200, d269471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68519 q ha hb
    | true =>
      simp only [d38200, d269471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h12 (q : Pattern) (ha : d38201 q = 1) (hb : d269472 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38201, d269472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d38201, d269472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d269473 q = 1) (hb : d270487 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269473, d270487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269473, d270487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269474 q = 1) (hb : d270488 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269474, d270488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269474, d270488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d269475 q = 1) (hb : d270489 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269475, d270489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269475, d270489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d269476 q = 1) (hb : d270490 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269476, d270490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269476, d270490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68521 (p : Pattern) (ha : d269481 p = 1) (hb : d270495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38200 q = 1) (hb : d269471 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38200, d269471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68519 q ha hb
    | true =>
      simp only [d38200, d269471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38201 q = 1) (hb : d269472 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38201, d269472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38201, d269472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269473 q = 1) (hb : d270487 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269473, d270487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269473, d270487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269474 q = 1) (hb : d270488 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269474, d270488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269474, d270488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d269475 q = 1) (hb : d270489 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269475, d270489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269475, d270489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d5239 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5243 q = 1) (hb : d269458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5243, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d2048 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d2061 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h21 (q : Pattern) (ha : d5244 q = 1) (hb : d269461 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5244, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5245 q = 1) (hb : d269462 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5245, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h23 (q : Pattern) (ha : d269481 q = 1) (hb : d270495 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269481, d270495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269481, d270495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro68522 (p : Pattern) (ha : d269488 p = 1) (hb : d270502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269477 q = 1) (hb : d270491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68520 q ha hb
    | true =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269478 q = 1) (hb : d270492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269479 q = 1) (hb : d270493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269479, d270493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269479, d270493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269480 q = 1) (hb : d270494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269480, d270494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269480, d270494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269484 q = 1) (hb : d270498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269484, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269484, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269485 q = 1) (hb : d270499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269485, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269485, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269486 q = 1) (hb : d270500 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269486, d270500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269486, d270500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269464 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
    | true =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269465 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269466 q = 1) (hb : d270483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269466, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269466, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269467 q = 1) (hb : d270484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269467, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269467, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269487 q = 1) (hb : d270501 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269487, d270501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269487, d270501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269488 q = 1) (hb : d270502 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269488, d270502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269488, d270502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68523 (p : Pattern) (ha : d269495 p = 1) (hb : d270509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h5 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d269492 q = 1) (hb : d270506 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269492, d270506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269492, d270506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269493 q = 1) (hb : d270507 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269493, d270507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269493, d270507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d269494 q = 1) (hb : d270508 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269494, d270508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269494, d270508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5239 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5243 q = 1) (hb : d269458 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5243, d269458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d2048 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2061 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h20 (q : Pattern) (ha : d5244 q = 1) (hb : d269461 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5244, d269461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d5245 q = 1) (hb : d269462 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d5245, d269462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d269495 q = 1) (hb : d270509 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269495, d270509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269495, d270509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  exact h22 p ha hb
theorem andIntro68524 (p : Pattern) (ha : d269504 p = 1) (hb : d270515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d269457 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5239, d269457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27181 q = 1) (hb : d269501 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d269501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27181, d269501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2061 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27182 q = 1) (hb : d269502 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27182, d269502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27182, d269502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27183 q = 1) (hb : d269503 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27183, d269503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27183, d269503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d269504 q = 1) (hb : d270515 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269504, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269504, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro68525 (p : Pattern) (ha : d269510 p = 1) (hb : d270521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269496 q = 1) (hb : d270510 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269496, d270510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68523 q ha hb
    | true =>
      simp only [d269496, d270510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269497 q = 1) (hb : d270511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269497, d270511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269497, d270511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269498 q = 1) (hb : d270512 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269498, d270512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269498, d270512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269499 q = 1) (hb : d270513 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269499, d270513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269499, d270513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269500 q = 1) (hb : d270514 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269500, d270514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269500, d270514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269505 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
    | true =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269506 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269507 q = 1) (hb : d270518 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269507, d270518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269507, d270518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269508 q = 1) (hb : d270519 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269508, d270519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269508, d270519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269509 q = 1) (hb : d270520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269509, d270520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269509, d270520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269510 q = 1) (hb : d270521 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269510, d270521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269510, d270521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro68526 (p : Pattern) (ha : d269516 p = 1) (hb : d270527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269484 q = 1) (hb : d270498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269484, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269484, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269485 q = 1) (hb : d270499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269485, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269485, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269515 q = 1) (hb : d270526 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269515, d270526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269515, d270526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269505 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
    | true =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269506 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269507 q = 1) (hb : d270518 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269507, d270518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269507, d270518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269508 q = 1) (hb : d270519 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269508, d270519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269508, d270519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269509 q = 1) (hb : d270520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269509, d270520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269509, d270520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269516 q = 1) (hb : d270527 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269516, d270527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269516, d270527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro68527 (p : Pattern) (ha : d269522 p = 1) (hb : d270533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269489 q = 1) (hb : d270503 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68518 q ha hb
    | true =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
  have h2 (q : Pattern) (ha : d269490 q = 1) (hb : d270504 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269491 q = 1) (hb : d270505 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269511 q = 1) (hb : d270522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
    | true =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68525 q ha hb
  have h5 (q : Pattern) (ha : d269512 q = 1) (hb : d270523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269513 q = 1) (hb : d270524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269514 q = 1) (hb : d270525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269517 q = 1) (hb : d270528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269517, d270528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
    | true =>
      simp only [d269517, d270528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68526 q ha hb
  have h9 (q : Pattern) (ha : d269518 q = 1) (hb : d270529 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269518, d270529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269518, d270529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269519 q = 1) (hb : d270530 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269519, d270530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269519, d270530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269520 q = 1) (hb : d270531 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269520, d270531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269520, d270531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269521 q = 1) (hb : d270532 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269521, d270532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269521, d270532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269522 q = 1) (hb : d270533 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269522, d270533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269522, d270533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro68528 (p : Pattern) (ha : d269526 p = 1) (hb : d270537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269517 q = 1) (hb : d270528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269517, d270528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
    | true =>
      simp only [d269517, d270528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68526 q ha hb
  have h2 (q : Pattern) (ha : d269518 q = 1) (hb : d270529 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269518, d270529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269518, d270529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269519 q = 1) (hb : d270530 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269519, d270530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269519, d270530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269520 q = 1) (hb : d270531 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269520, d270531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269520, d270531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269525 q = 1) (hb : d270536 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269525, d270536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269525, d270536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269526 q = 1) (hb : d270537 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269526, d270537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269526, d270537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68529 (p : Pattern) (ha : d269532 p = 1) (hb : d270543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d270534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68527 q ha hb
    | true =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d270535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d270540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d270541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269531 q = 1) (hb : d270542 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269531, d270542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269531, d270542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269532 q = 1) (hb : d270543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269532, d270543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269532, d270543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68530 (p : Pattern) (ha : d269536 p = 1) (hb : d270547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d270544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d270545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269535 q = 1) (hb : d270546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269535, d270546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269535, d270546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269536 q = 1) (hb : d270547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269536, d270547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269536, d270547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68531 (p : Pattern) (ha : d269542 p = 1) (hb : d270553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269537 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68529 q ha hb
    | true =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
  have h2 (q : Pattern) (ha : d269538 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269538, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269538, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269539 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269539, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269539, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269540 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269540, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269540, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269541 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269541, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269541, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269542 q = 1) (hb : d270553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269542, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269542, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68532 (p : Pattern) (ha : d269545 p = 1) (hb : d270556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d270534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68527 q ha hb
    | true =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d270535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d270540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d270541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269531 q = 1) (hb : d270542 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269531, d270542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269531, d270542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269545 q = 1) (hb : d270556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269545, d270556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269545, d270556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68533 (p : Pattern) (ha : d269546 p = 1) (hb : d270557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d270544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d270545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269535 q = 1) (hb : d270546 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269535, d270546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269535, d270546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269546 q = 1) (hb : d270557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269546, d270557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269546, d270557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68534 (p : Pattern) (ha : d269552 p = 1) (hb : d270563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269537 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68529 q ha hb
    | true =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
  have h2 (q : Pattern) (ha : d269538 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269538, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269538, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269539 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269539, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269539, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269540 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269540, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269540, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269541 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269541, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269541, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269547 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269547, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68532 q ha hb
    | true =>
      simp only [d269547, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68533 q ha hb
  have h7 (q : Pattern) (ha : d269548 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269548, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269548, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269549 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269549, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269549, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269550 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269550, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269550, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269551 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269551, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269551, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269552 q = 1) (hb : d270563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269552, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269552, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro68535 (p : Pattern) (ha : d269557 p = 1) (hb : d270568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d270534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68527 q ha hb
    | true =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d270535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d270540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d270541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269556 q = 1) (hb : d270567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269556, d270567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269556, d270567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269557 q = 1) (hb : d270568 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269557, d270568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269557, d270568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68536 (p : Pattern) (ha : d269559 p = 1) (hb : d270570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d270544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d270545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269558 q = 1) (hb : d270569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269558, d270569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269558, d270569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269559 q = 1) (hb : d270570 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269559, d270570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269559, d270570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68537 (p : Pattern) (ha : d269566 p = 1) (hb : d270577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d270534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68527 q ha hb
    | true =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d270535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d270540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269564 q = 1) (hb : d270575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269564, d270575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269564, d270575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269565 q = 1) (hb : d270576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269565, d270576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269565, d270576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269566 q = 1) (hb : d270577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269566, d270577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269566, d270577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68538 (p : Pattern) (ha : d269569 p = 1) (hb : d270580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d270544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269567 q = 1) (hb : d270578 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269567, d270578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269567, d270578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269568 q = 1) (hb : d270579 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269568, d270579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269568, d270579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269569 q = 1) (hb : d270580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269569, d270580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269569, d270580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68539 (p : Pattern) (ha : d269578 p = 1) (hb : d270587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269464 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
    | true =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d269465 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d269466 q = 1) (hb : d270483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269466, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269466, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269467 q = 1) (hb : d270484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269467, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269467, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d269468 q = 1) (hb : d270485 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269468, d270485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269468, d270485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269487 q = 1) (hb : d270501 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269487, d270501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269487, d270501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d269578 q = 1) (hb : d270587 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269578, d270587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269578, d270587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68540 (p : Pattern) (ha : d269584 p = 1) (hb : d270593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269575 q = 1) (hb : d270584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269575, d270584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269575, d270584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68518 q ha hb
  have h3 (q : Pattern) (ha : d269576 q = 1) (hb : d270585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269576, d270585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269576, d270585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269577 q = 1) (hb : d270586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269577, d270586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269577, d270586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269579 q = 1) (hb : d270588 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269579, d270588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68518 q ha hb
    | true =>
      simp only [d269579, d270588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68539 q ha hb
  have h6 (q : Pattern) (ha : d269580 q = 1) (hb : d270589 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269580, d270589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269580, d270589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269581 q = 1) (hb : d270590 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269581, d270590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269581, d270590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269582 q = 1) (hb : d270591 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269582, d270591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269582, d270591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269489 q = 1) (hb : d270503 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68518 q ha hb
    | true =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
  have h10 (q : Pattern) (ha : d269490 q = 1) (hb : d270504 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269491 q = 1) (hb : d270505 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269511 q = 1) (hb : d270522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
    | true =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68525 q ha hb
  have h13 (q : Pattern) (ha : d269512 q = 1) (hb : d270523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269513 q = 1) (hb : d270524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269514 q = 1) (hb : d270525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269583 q = 1) (hb : d270592 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269583, d270592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269583, d270592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269584 q = 1) (hb : d270593 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269584, d270593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269584, d270593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro68541 (p : Pattern) (ha : d269589 p = 1) (hb : d270598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269489 q = 1) (hb : d270503 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68518 q ha hb
    | true =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
  have h2 (q : Pattern) (ha : d269490 q = 1) (hb : d270504 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269491 q = 1) (hb : d270505 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269511 q = 1) (hb : d270522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
    | true =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68525 q ha hb
  have h5 (q : Pattern) (ha : d269512 q = 1) (hb : d270523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269513 q = 1) (hb : d270524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269514 q = 1) (hb : d270525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269587 q = 1) (hb : d270596 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269587, d270596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269587, d270596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269588 q = 1) (hb : d270597 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269588, d270597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269588, d270597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269589 q = 1) (hb : d270598 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269589, d270598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269589, d270598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro68542 (p : Pattern) (ha : d269595 p = 1) (hb : d270604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269585 q = 1) (hb : d270594 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269585, d270594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68540 q ha hb
    | true =>
      simp only [d269585, d270594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269586 q = 1) (hb : d270595 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269586, d270595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269586, d270595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269590 q = 1) (hb : d270599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68541 q ha hb
    | true =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269591 q = 1) (hb : d270600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269592 q = 1) (hb : d270601 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269592, d270601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269592, d270601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269593 q = 1) (hb : d270602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269593, d270602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269593, d270602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269594 q = 1) (hb : d270603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269594, d270603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269594, d270603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269595 q = 1) (hb : d270604 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269595, d270604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269595, d270604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68543 (p : Pattern) (ha : d269599 p = 1) (hb : d270608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269590 q = 1) (hb : d270599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68541 q ha hb
    | true =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269591 q = 1) (hb : d270600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269596 q = 1) (hb : d270605 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269596, d270605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269596, d270605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269597 q = 1) (hb : d270606 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269597, d270606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269597, d270606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269598 q = 1) (hb : d270607 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269598, d270607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269598, d270607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269599 q = 1) (hb : d270608 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269599, d270608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269599, d270608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68544 (p : Pattern) (ha : d269602 p = 1) (hb : d270480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269454 q = 1) (hb : d270477 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269454, d270477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269454, d270477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d269455 q = 1) (hb : d270478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269455, d270478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269455, d270478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d269456 q = 1) (hb : d270479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269456, d270479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269456, d270479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
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
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d269602 q = 1) (hb : d270480 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269602, d270480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269602, d270480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro68545 (p : Pattern) (ha : d269608 p = 1) (hb : d270502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269477 q = 1) (hb : d270491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68520 q ha hb
    | true =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269478 q = 1) (hb : d270492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269479 q = 1) (hb : d270493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269479, d270493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269479, d270493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269480 q = 1) (hb : d270494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269480, d270494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269480, d270494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269484 q = 1) (hb : d270498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269484, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269484, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269485 q = 1) (hb : d270499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269485, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269485, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269486 q = 1) (hb : d270500 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269486, d270500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269486, d270500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269603 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269603, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68544 q ha hb
    | true =>
      simp only [d269603, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269604 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269604, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269604, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269605 q = 1) (hb : d270483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269605, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269605, d270483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269606 q = 1) (hb : d270484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269606, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269606, d270484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269607 q = 1) (hb : d270501 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269607, d270501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269607, d270501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269608 q = 1) (hb : d270502 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269608, d270502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269608, d270502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68546 (p : Pattern) (ha : d269609 p = 1) (hb : d270495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d38157 q = 1) (hb : d269428 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68514 q ha hb
    | true =>
      simp only [d38157, d269428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38158 q = 1) (hb : d269453 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38158, d269453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38200 q = 1) (hb : d269471 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38200, d269471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68519 q ha hb
    | true =>
      simp only [d38200, d269471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38201 q = 1) (hb : d269472 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38201, d269472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38201, d269472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269473 q = 1) (hb : d270487 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d269473, d270487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269473, d270487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269474 q = 1) (hb : d270488 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d269474, d270488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269474, d270488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d269475 q = 1) (hb : d270489 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d269475, d270489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269475, d270489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h15 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h20 (q : Pattern) (ha : d269609 q = 1) (hb : d270495 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269609, d270495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269609, d270495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro68547 (p : Pattern) (ha : d269615 p = 1) (hb : d270611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269610 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269610, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68546 q ha hb
    | true =>
      simp only [d269610, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269611 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269611, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269611, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269612 q = 1) (hb : d270498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269612, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269612, d270498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269613 q = 1) (hb : d270499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269613, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269613, d270499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269614 q = 1) (hb : d270526 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269614, d270526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269614, d270526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269615 q = 1) (hb : d270611 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269615, d270611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269615, d270611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68548 (p : Pattern) (ha : d269621 p = 1) (hb : d270617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269489 q = 1) (hb : d270503 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68518 q ha hb
    | true =>
      simp only [d269489, d270503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
  have h2 (q : Pattern) (ha : d269490 q = 1) (hb : d270504 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269490, d270504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269491 q = 1) (hb : d270505 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269491, d270505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269511 q = 1) (hb : d270522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68522 q ha hb
    | true =>
      simp only [d269511, d270522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68525 q ha hb
  have h5 (q : Pattern) (ha : d269512 q = 1) (hb : d270523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269512, d270523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269513 q = 1) (hb : d270524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269513, d270524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269514 q = 1) (hb : d270525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269514, d270525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269616 q = 1) (hb : d270612 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269616, d270612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68545 q ha hb
    | true =>
      simp only [d269616, d270612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68547 q ha hb
  have h9 (q : Pattern) (ha : d269617 q = 1) (hb : d270613 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269617, d270613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269617, d270613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269618 q = 1) (hb : d270614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269618, d270614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269618, d270614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269619 q = 1) (hb : d270615 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269619, d270615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269619, d270615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269620 q = 1) (hb : d270616 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269620, d270616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269620, d270616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269621 q = 1) (hb : d270617 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269621, d270617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269621, d270617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro68549 (p : Pattern) (ha : d269627 p = 1) (hb : d270623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269622 q = 1) (hb : d270618 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269622, d270618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68548 q ha hb
    | true =>
      simp only [d269622, d270618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269623 q = 1) (hb : d270619 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269623, d270619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269623, d270619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269624 q = 1) (hb : d270620 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269624, d270620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269624, d270620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269625 q = 1) (hb : d270621 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269625, d270621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269625, d270621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269626 q = 1) (hb : d270622 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269626, d270622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269626, d270622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269627 q = 1) (hb : d270623 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269627, d270623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269627, d270623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68550 (p : Pattern) (ha : d269633 p = 1) (hb : d270629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269560 q = 1) (hb : d270571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269560, d270571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68535 q ha hb
    | true =>
      simp only [d269560, d270571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68536 q ha hb
  have h2 (q : Pattern) (ha : d269561 q = 1) (hb : d270572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269561, d270572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269561, d270572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269562 q = 1) (hb : d270573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269562, d270573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269562, d270573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269563 q = 1) (hb : d270574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269563, d270574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269563, d270574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269570 q = 1) (hb : d270581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269570, d270581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68537 q ha hb
    | true =>
      simp only [d269570, d270581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68538 q ha hb
  have h6 (q : Pattern) (ha : d269571 q = 1) (hb : d270582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269571, d270582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269571, d270582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269572 q = 1) (hb : d270583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269572, d270583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269572, d270583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269600 q = 1) (hb : d270609 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269600, d270609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68542 q ha hb
    | true =>
      simp only [d269600, d270609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68543 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269601 q = 1) (hb : d270610 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d270610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269601, d270610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269628 q = 1) (hb : d270624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269628, d270624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68549 q ha hb
    | true =>
      simp only [d269628, d270624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269629 q = 1) (hb : d270625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269629, d270625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269629, d270625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269630 q = 1) (hb : d270626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d270626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269630, d270626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269631 q = 1) (hb : d270627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d270627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269631, d270627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269632 q = 1) (hb : d270628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d270628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269632, d270628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269633 q = 1) (hb : d270629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269633, d270629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269633, d270629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro68551 (p : Pattern) (ha : d269634 p = 1) (hb : d270630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d270534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68527 q ha hb
    | true =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d270535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d270540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269530 q = 1) (hb : d270541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269530, d270541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269556 q = 1) (hb : d270567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269556, d270567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269556, d270567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269634 q = 1) (hb : d270630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269634, d270630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269634, d270630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68552 (p : Pattern) (ha : d269635 p = 1) (hb : d270631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d270544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269534 q = 1) (hb : d270545 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269534, d270545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269558 q = 1) (hb : d270569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269558, d270569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269558, d270569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269635 q = 1) (hb : d270631 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269635, d270631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269635, d270631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68553 (p : Pattern) (ha : d269640 p = 1) (hb : d270636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269523 q = 1) (hb : d270534 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68527 q ha hb
    | true =>
      simp only [d269523, d270534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269524 q = 1) (hb : d270535 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269524, d270535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269529 q = 1) (hb : d270540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269529, d270540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269564 q = 1) (hb : d270575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269564, d270575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269564, d270575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269565 q = 1) (hb : d270576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269565, d270576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269565, d270576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269640 q = 1) (hb : d270636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269640, d270636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269640, d270636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68554 (p : Pattern) (ha : d269641 p = 1) (hb : d270637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269533 q = 1) (hb : d270544 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269533, d270544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269567 q = 1) (hb : d270578 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269567, d270578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269567, d270578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269568 q = 1) (hb : d270579 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269568, d270579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269568, d270579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269641 q = 1) (hb : d270637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269641, d270637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269641, d270637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68555 (p : Pattern) (ha : d269645 p = 1) (hb : d270641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269585 q = 1) (hb : d270594 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269585, d270594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68540 q ha hb
    | true =>
      simp only [d269585, d270594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269586 q = 1) (hb : d270595 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269586, d270595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269586, d270595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269590 q = 1) (hb : d270599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68541 q ha hb
    | true =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269591 q = 1) (hb : d270600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269592 q = 1) (hb : d270601 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269592, d270601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269592, d270601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269593 q = 1) (hb : d270602 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269593, d270602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269593, d270602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269594 q = 1) (hb : d270603 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269594, d270603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269594, d270603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269645 q = 1) (hb : d270641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269645, d270641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269645, d270641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68556 (p : Pattern) (ha : d269646 p = 1) (hb : d270642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269590 q = 1) (hb : d270599 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68541 q ha hb
    | true =>
      simp only [d269590, d270599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269591 q = 1) (hb : d270600 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269591, d270600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269527 q = 1) (hb : d270538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68528 q ha hb
    | true =>
      simp only [d269527, d270538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269528 q = 1) (hb : d270539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269528, d270539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269596 q = 1) (hb : d270605 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269596, d270605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269596, d270605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269597 q = 1) (hb : d270606 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269597, d270606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269597, d270606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269598 q = 1) (hb : d270607 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269598, d270607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269598, d270607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269646 q = 1) (hb : d270642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269646, d270642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269646, d270642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68557 (p : Pattern) (ha : d269649 p = 1) (hb : d270645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269622 q = 1) (hb : d270618 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269622, d270618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68548 q ha hb
    | true =>
      simp only [d269622, d270618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269623 q = 1) (hb : d270619 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269623, d270619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269623, d270619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269624 q = 1) (hb : d270620 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269624, d270620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269624, d270620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269625 q = 1) (hb : d270621 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269625, d270621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269625, d270621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269626 q = 1) (hb : d270622 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269626, d270622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269626, d270622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269649 q = 1) (hb : d270645 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269649, d270645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269649, d270645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68558 (p : Pattern) (ha : d269655 p = 1) (hb : d270651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269560 q = 1) (hb : d270571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269560, d270571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68535 q ha hb
    | true =>
      simp only [d269560, d270571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68536 q ha hb
  have h2 (q : Pattern) (ha : d269561 q = 1) (hb : d270572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269561, d270572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269561, d270572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269562 q = 1) (hb : d270573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269562, d270573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269562, d270573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269563 q = 1) (hb : d270574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269563, d270574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269563, d270574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269570 q = 1) (hb : d270581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269570, d270581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68537 q ha hb
    | true =>
      simp only [d269570, d270581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68538 q ha hb
  have h6 (q : Pattern) (ha : d269571 q = 1) (hb : d270582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269571, d270582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269571, d270582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269572 q = 1) (hb : d270583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269572, d270583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269572, d270583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269600 q = 1) (hb : d270609 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269600, d270609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68542 q ha hb
    | true =>
      simp only [d269600, d270609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68543 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269537 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d269601 q = 1) (hb : d270610 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d270610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269601, d270610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d269628 q = 1) (hb : d270624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269628, d270624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68549 q ha hb
    | true =>
      simp only [d269628, d270624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269629 q = 1) (hb : d270625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269629, d270625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269629, d270625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269630 q = 1) (hb : d270626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d270626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269630, d270626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269631 q = 1) (hb : d270627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d270627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269631, d270627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269632 q = 1) (hb : d270628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d270628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269632, d270628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269636 q = 1) (hb : d270632 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269636, d270632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68551 q ha hb
    | true =>
      simp only [d269636, d270632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68552 q ha hb
  have h17 (q : Pattern) (ha : d269637 q = 1) (hb : d270633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269637, d270633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269637, d270633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269638 q = 1) (hb : d270634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269638, d270634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269638, d270634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d269639 q = 1) (hb : d270635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269639, d270635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269639, d270635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269642 q = 1) (hb : d270638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269642, d270638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68553 q ha hb
    | true =>
      simp only [d269642, d270638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68554 q ha hb
  have h21 (q : Pattern) (ha : d269643 q = 1) (hb : d270639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269643, d270639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269643, d270639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269644 q = 1) (hb : d270640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269644, d270640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269644, d270640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269647 q = 1) (hb : d270643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269647, d270643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68555 q ha hb
    | true =>
      simp only [d269647, d270643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68556 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d269648 q = 1) (hb : d270644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d270644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269648, d270644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d269650 q = 1) (hb : d270646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269650, d270646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68557 q ha hb
    | true =>
      simp only [d269650, d270646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d269651 q = 1) (hb : d270647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269651, d270647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d269651, d270647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d269652 q = 1) (hb : d270648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d270648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d269652, d270648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d269653 q = 1) (hb : d270649 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269653, d270649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269653, d270649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d269654 q = 1) (hb : d270650 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269654, d270650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269654, d270650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d269655 q = 1) (hb : d270651 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269655, d270651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269655, d270651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro68559 (p : Pattern) (ha : d269667 p = 1) (hb : d270663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269657 q = 1) (hb : d270653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269657, d270653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68543 q ha hb
    | true =>
      simp only [d269657, d270653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
  have h2 (q : Pattern) (ha : d269658 q = 1) (hb : d270654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269658, d270654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269658, d270654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269659 q = 1) (hb : d270655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269659, d270655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269659, d270655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269660 q = 1) (hb : d270656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269660, d270656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269660, d270656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269661 q = 1) (hb : d270657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269661, d270657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269661, d270657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269662 q = 1) (hb : d270658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269662, d270658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
    | true =>
      simp only [d269662, d270658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269663 q = 1) (hb : d270659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269663, d270659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269663, d270659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269664 q = 1) (hb : d270660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269664, d270660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269664, d270660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269665 q = 1) (hb : d270661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269665, d270661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269665, d270661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269666 q = 1) (hb : d270662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269666, d270662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269666, d270662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269667 q = 1) (hb : d270663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269667, d270663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269667, d270663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro68560 (p : Pattern) (ha : d269673 p = 1) (hb : d270669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269662 q = 1) (hb : d270658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269662, d270658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
    | true =>
      simp only [d269662, d270658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269663 q = 1) (hb : d270659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269663, d270659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269663, d270659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269664 q = 1) (hb : d270660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269664, d270660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269664, d270660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269665 q = 1) (hb : d270661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269665, d270661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269665, d270661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269666 q = 1) (hb : d270662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269666, d270662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269666, d270662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269668 q = 1) (hb : d270664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269668, d270664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68533 q ha hb
    | true =>
      simp only [d269668, d270664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269669 q = 1) (hb : d270665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269669, d270665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269669, d270665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269670 q = 1) (hb : d270666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269670, d270666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269670, d270666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269671 q = 1) (hb : d270667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269671, d270667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269671, d270667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269672 q = 1) (hb : d270668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269672, d270668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269672, d270668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269673 q = 1) (hb : d270669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269673, d270669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269673, d270669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro68561 (p : Pattern) (ha : d269680 p = 1) (hb : d270676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269647 q = 1) (hb : d270643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269647, d270643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68555 q ha hb
    | true =>
      simp only [d269647, d270643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68556 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269648 q = 1) (hb : d270644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d270644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269648, d270644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269650 q = 1) (hb : d270646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269650, d270646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68557 q ha hb
    | true =>
      simp only [d269650, d270646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269651 q = 1) (hb : d270647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269651, d270647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269651, d270647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269652 q = 1) (hb : d270648 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d270648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269652, d270648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269678 q = 1) (hb : d270674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269678, d270674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269678, d270674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269679 q = 1) (hb : d270675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269679, d270675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269679, d270675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269680 q = 1) (hb : d270676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269680, d270676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269680, d270676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro68562 (p : Pattern) (ha : d269682 p = 1) (hb : d270678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269668 q = 1) (hb : d270664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269668, d270664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68533 q ha hb
    | true =>
      simp only [d269668, d270664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269669 q = 1) (hb : d270665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269669, d270665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269669, d270665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269670 q = 1) (hb : d270666 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269670, d270666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269670, d270666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269671 q = 1) (hb : d270667 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269671, d270667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269671, d270667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269672 q = 1) (hb : d270668 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269672, d270668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269672, d270668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269682 q = 1) (hb : d270678 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269682, d270678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269682, d270678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68563 (p : Pattern) (ha : d269708 p = 1) (hb : d270694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38538 q = 1) (hb : d269694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38538, d269694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38538, d269694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68515 q ha hb
  have h2 (q : Pattern) (ha : d38163 q = 1) (hb : d269434 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38163, d269434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68515 q ha hb
    | true =>
      simp only [d38163, d269434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38539 q = 1) (hb : d269695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38539, d269695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38539, d269695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38164 q = 1) (hb : d269435 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38164, d269435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38164, d269435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38540 q = 1) (hb : d269696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38540, d269696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38540, d269696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38541 q = 1) (hb : d269697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38541, d269697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38541, d269697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d269698 q = 1) (hb : d270684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269698, d270684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269698, d270684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68516 q ha hb
  have h8 (q : Pattern) (ha : d269443 q = 1) (hb : d270472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269443, d270472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68516 q ha hb
    | true =>
      simp only [d269443, d270472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269699 q = 1) (hb : d270685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269699, d270685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269699, d270685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269444 q = 1) (hb : d270473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269444, d270473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269444, d270473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269700 q = 1) (hb : d270686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269700, d270686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269700, d270686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269701 q = 1) (hb : d270687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269701, d270687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269701, d270687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269702 q = 1) (hb : d270688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269702, d270688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269702, d270688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269691 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269703 q = 1) (hb : d270689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269703, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269703, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
  have h16 (q : Pattern) (ha : d269464 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
    | true =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d269704 q = 1) (hb : d270690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269704, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269704, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269465 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d269705 q = 1) (hb : d270691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269705, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269705, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269706 q = 1) (hb : d270692 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269706, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269706, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269707 q = 1) (hb : d270693 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269707, d270693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d269707, d270693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d269708 q = 1) (hb : d270694 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269708, d270694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269708, d270694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro68564 (p : Pattern) (ha : d269713 p = 1) (hb : d270699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269691 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269703 q = 1) (hb : d270689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269703, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269703, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
  have h3 (q : Pattern) (ha : d269464 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
    | true =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d269704 q = 1) (hb : d270690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269704, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269704, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269465 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d269705 q = 1) (hb : d270691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269705, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269705, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269706 q = 1) (hb : d270692 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269706, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269706, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d269707 q = 1) (hb : d270693 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269707, d270693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269707, d270693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269712 q = 1) (hb : d270698 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269712, d270698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269712, d270698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d269713 q = 1) (hb : d270699 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269713, d270699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269713, d270699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68565 (p : Pattern) (ha : d269727 p = 1) (hb : d270713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269718 q = 1) (hb : d270704 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269718, d270704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269718, d270704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68520 q ha hb
  have h2 (q : Pattern) (ha : d269477 q = 1) (hb : d270491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68520 q ha hb
    | true =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269719 q = 1) (hb : d270705 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269719, d270705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269719, d270705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269478 q = 1) (hb : d270492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269720 q = 1) (hb : d270706 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269720, d270706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269720, d270706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269721 q = 1) (hb : d270707 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269721, d270707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269721, d270707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269722 q = 1) (hb : d270708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
  have h8 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269723 q = 1) (hb : d270709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269724 q = 1) (hb : d270710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269725 q = 1) (hb : d270711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269726 q = 1) (hb : d270712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269726, d270712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269726, d270712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269703 q = 1) (hb : d270689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269703, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269703, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
  have h15 (q : Pattern) (ha : d269464 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68517 q ha hb
    | true =>
      simp only [d269464, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269704 q = 1) (hb : d270690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269704, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269704, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269465 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269465, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269705 q = 1) (hb : d270691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269705, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269705, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269706 q = 1) (hb : d270692 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269706, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269706, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269712 q = 1) (hb : d270698 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269712, d270698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269712, d270698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269727 q = 1) (hb : d270713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269727, d270713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269727, d270713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro68566 (p : Pattern) (ha : d269741 p = 1) (hb : d270727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269731 q = 1) (hb : d270717 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269731, d270717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269731, d270717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68523 q ha hb
  have h2 (q : Pattern) (ha : d269496 q = 1) (hb : d270510 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269496, d270510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68523 q ha hb
    | true =>
      simp only [d269496, d270510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269732 q = 1) (hb : d270718 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269732, d270718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269732, d270718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269497 q = 1) (hb : d270511 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269497, d270511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269497, d270511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269733 q = 1) (hb : d270719 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269733, d270719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269733, d270719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269734 q = 1) (hb : d270720 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269734, d270720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269734, d270720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269735 q = 1) (hb : d270721 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269735, d270721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269735, d270721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269736 q = 1) (hb : d270722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269736, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269736, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
  have h9 (q : Pattern) (ha : d269505 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
    | true =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269737 q = 1) (hb : d270723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269737, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269737, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269506 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269738 q = 1) (hb : d270724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269738, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269738, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269739 q = 1) (hb : d270725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269739, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269739, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269740 q = 1) (hb : d270726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269740, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269740, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269741 q = 1) (hb : d270727 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269741, d270727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269741, d270727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68567 (p : Pattern) (ha : d269747 p = 1) (hb : d270733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269709 q = 1) (hb : d270695 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269709, d270695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269709, d270695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68563 q ha hb
  have h3 (q : Pattern) (ha : d269710 q = 1) (hb : d270696 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269710, d270696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269710, d270696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269711 q = 1) (hb : d270697 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269711, d270697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269711, d270697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269714 q = 1) (hb : d270700 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269714, d270700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68563 q ha hb
    | true =>
      simp only [d269714, d270700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68564 q ha hb
  have h6 (q : Pattern) (ha : d269715 q = 1) (hb : d270701 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269715, d270701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269715, d270701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269716 q = 1) (hb : d270702 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269716, d270702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269716, d270702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269717 q = 1) (hb : d270703 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269717, d270703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269717, d270703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269728 q = 1) (hb : d270714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68563 q ha hb
    | true =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
  have h10 (q : Pattern) (ha : d269729 q = 1) (hb : d270715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269730 q = 1) (hb : d270716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269742 q = 1) (hb : d270728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68566 q ha hb
  have h13 (q : Pattern) (ha : d269743 q = 1) (hb : d270729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269744 q = 1) (hb : d270730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269745 q = 1) (hb : d270731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269746 q = 1) (hb : d270732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269746, d270732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269746, d270732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269747 q = 1) (hb : d270733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269747, d270733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269747, d270733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro68568 (p : Pattern) (ha : d269752 p = 1) (hb : d270738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269728 q = 1) (hb : d270714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68563 q ha hb
    | true =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
  have h2 (q : Pattern) (ha : d269729 q = 1) (hb : d270715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269730 q = 1) (hb : d270716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269742 q = 1) (hb : d270728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68566 q ha hb
  have h5 (q : Pattern) (ha : d269743 q = 1) (hb : d270729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269744 q = 1) (hb : d270730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269745 q = 1) (hb : d270731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269750 q = 1) (hb : d270736 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269750, d270736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269750, d270736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269751 q = 1) (hb : d270737 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269751, d270737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269751, d270737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269752 q = 1) (hb : d270738 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269752, d270738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269752, d270738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro68569 (p : Pattern) (ha : d269758 p = 1) (hb : d270744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269748 q = 1) (hb : d270734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269748, d270734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68567 q ha hb
    | true =>
      simp only [d269748, d270734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269749 q = 1) (hb : d270735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269749, d270735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269749, d270735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269753 q = 1) (hb : d270739 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269753, d270739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68568 q ha hb
    | true =>
      simp only [d269753, d270739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269754 q = 1) (hb : d270740 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269754, d270740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269754, d270740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269755 q = 1) (hb : d270741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269755, d270741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269755, d270741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269756 q = 1) (hb : d270742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269756, d270742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269756, d270742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269757 q = 1) (hb : d270743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269757, d270743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269757, d270743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269758 q = 1) (hb : d270744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269758, d270744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269758, d270744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68570 (p : Pattern) (ha : d269760 p = 1) (hb : d270746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269722 q = 1) (hb : d270708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
  have h2 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269723 q = 1) (hb : d270709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269724 q = 1) (hb : d270710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269725 q = 1) (hb : d270711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269759 q = 1) (hb : d270745 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269759, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269759, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269736 q = 1) (hb : d270722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269736, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269736, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
  have h9 (q : Pattern) (ha : d269505 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
    | true =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269737 q = 1) (hb : d270723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269737, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269737, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269506 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269506, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269738 q = 1) (hb : d270724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269738, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269738, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269739 q = 1) (hb : d270725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269739, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269739, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d269740 q = 1) (hb : d270726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269740, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269740, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269760 q = 1) (hb : d270746 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269760, d270746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269760, d270746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68571 (p : Pattern) (ha : d269766 p = 1) (hb : d270752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269761 q = 1) (hb : d270747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269761, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269761, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68570 q ha hb
  have h2 (q : Pattern) (ha : d269762 q = 1) (hb : d270748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269762, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269762, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269763 q = 1) (hb : d270749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269763, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269763, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269764 q = 1) (hb : d270750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269764, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269764, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269765 q = 1) (hb : d270751 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269765, d270751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269765, d270751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269766 q = 1) (hb : d270752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269766, d270752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269766, d270752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68572 (p : Pattern) (ha : d269772 p = 1) (hb : d270758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269753 q = 1) (hb : d270739 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269753, d270739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68568 q ha hb
    | true =>
      simp only [d269753, d270739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269754 q = 1) (hb : d270740 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269754, d270740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269754, d270740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269767 q = 1) (hb : d270753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269767, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68571 q ha hb
    | true =>
      simp only [d269767, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269768 q = 1) (hb : d270754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269768, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269768, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269769 q = 1) (hb : d270755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269769, d270755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269769, d270755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269770 q = 1) (hb : d270756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269770, d270756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269770, d270756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269771 q = 1) (hb : d270757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269771, d270757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269771, d270757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269772 q = 1) (hb : d270758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269772, d270758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269772, d270758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68573 (p : Pattern) (ha : d269815 p = 1) (hb : d270713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269718 q = 1) (hb : d270704 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269718, d270704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269718, d270704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68520 q ha hb
  have h2 (q : Pattern) (ha : d269477 q = 1) (hb : d270491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68520 q ha hb
    | true =>
      simp only [d269477, d270491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269719 q = 1) (hb : d270705 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269719, d270705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269719, d270705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269478 q = 1) (hb : d270492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269478, d270492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269720 q = 1) (hb : d270706 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269720, d270706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269720, d270706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269721 q = 1) (hb : d270707 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269721, d270707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269721, d270707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269722 q = 1) (hb : d270708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
  have h8 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d269723 q = 1) (hb : d270709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d269724 q = 1) (hb : d270710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269725 q = 1) (hb : d270711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269726 q = 1) (hb : d270712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269726, d270712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269726, d270712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269810 q = 1) (hb : d270689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269810, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269810, d270689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68544 q ha hb
  have h15 (q : Pattern) (ha : d269603 q = 1) (hb : d270481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269603, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68544 q ha hb
    | true =>
      simp only [d269603, d270481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269811 q = 1) (hb : d270690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269811, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269811, d270690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269604 q = 1) (hb : d270482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269604, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269604, d270482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d269812 q = 1) (hb : d270691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269812, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269812, d270691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269813 q = 1) (hb : d270692 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269813, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269813, d270692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d269814 q = 1) (hb : d270698 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269814, d270698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269814, d270698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269815 q = 1) (hb : d270713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269815, d270713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269815, d270713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro68574 (p : Pattern) (ha : d269821 p = 1) (hb : d270761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269816 q = 1) (hb : d270708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269816, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269816, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68546 q ha hb
  have h2 (q : Pattern) (ha : d269610 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269610, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68546 q ha hb
    | true =>
      simp only [d269610, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269817 q = 1) (hb : d270709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269817, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269817, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269611 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269611, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269611, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269818 q = 1) (hb : d270710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269818, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269818, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269819 q = 1) (hb : d270711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269819, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269819, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269820 q = 1) (hb : d270745 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269820, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269820, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269821 q = 1) (hb : d270761 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269821, d270761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269821, d270761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68575 (p : Pattern) (ha : d269827 p = 1) (hb : d270767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269728 q = 1) (hb : d270714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68563 q ha hb
    | true =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
  have h2 (q : Pattern) (ha : d269729 q = 1) (hb : d270715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269730 q = 1) (hb : d270716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269742 q = 1) (hb : d270728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68566 q ha hb
  have h5 (q : Pattern) (ha : d269743 q = 1) (hb : d270729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269744 q = 1) (hb : d270730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269745 q = 1) (hb : d270731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269822 q = 1) (hb : d270762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269822, d270762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68573 q ha hb
    | true =>
      simp only [d269822, d270762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68574 q ha hb
  have h9 (q : Pattern) (ha : d269823 q = 1) (hb : d270763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269823, d270763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269823, d270763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269824 q = 1) (hb : d270764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269824, d270764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269824, d270764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269825 q = 1) (hb : d270765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269825, d270765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269825, d270765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269826 q = 1) (hb : d270766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269826, d270766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269826, d270766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269827 q = 1) (hb : d270767 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269827, d270767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269827, d270767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro68576 (p : Pattern) (ha : d269833 p = 1) (hb : d270773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269828 q = 1) (hb : d270768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269828, d270768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68575 q ha hb
    | true =>
      simp only [d269828, d270768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269829 q = 1) (hb : d270769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269829, d270769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269829, d270769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269830 q = 1) (hb : d270770 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269830, d270770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269830, d270770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269831 q = 1) (hb : d270771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269831, d270771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269831, d270771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269832 q = 1) (hb : d270772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269832, d270772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269832, d270772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269833 q = 1) (hb : d270773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269833, d270773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269833, d270773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68577 (p : Pattern) (ha : d269839 p = 1) (hb : d270779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269773 q = 1) (hb : d270759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269773, d270759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68569 q ha hb
    | true =>
      simp only [d269773, d270759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269809 q = 1) (hb : d270760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269809, d270760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269809, d270760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d269834 q = 1) (hb : d270774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269834, d270774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68576 q ha hb
    | true =>
      simp only [d269834, d270774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269835 q = 1) (hb : d270775 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269835, d270775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269835, d270775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269836 q = 1) (hb : d270776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269836, d270776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269836, d270776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269837 q = 1) (hb : d270777 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269837, d270777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269837, d270777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269838 q = 1) (hb : d270778 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269838, d270778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269838, d270778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269839 q = 1) (hb : d270779 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269839, d270779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269839, d270779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro68578 (p : Pattern) (ha : d269844 p = 1) (hb : d270784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269767 q = 1) (hb : d270753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269767, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68571 q ha hb
    | true =>
      simp only [d269767, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269768 q = 1) (hb : d270754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269768, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269768, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269841 q = 1) (hb : d270781 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269841, d270781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269841, d270781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269842 q = 1) (hb : d270782 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269842, d270782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269842, d270782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269843 q = 1) (hb : d270783 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269843, d270783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269843, d270783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269844 q = 1) (hb : d270784 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269844, d270784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269844, d270784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68579 (p : Pattern) (ha : d269850 p = 1) (hb : d270790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269845 q = 1) (hb : d270785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269845, d270785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68578 q ha hb
    | true =>
      simp only [d269845, d270785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269846 q = 1) (hb : d270786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269846, d270786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269846, d270786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269847 q = 1) (hb : d270787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269847, d270787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269847, d270787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269848 q = 1) (hb : d270788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269848, d270788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269848, d270788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269849 q = 1) (hb : d270789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269849, d270789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269849, d270789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269850 q = 1) (hb : d270790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269850, d270790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269850, d270790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68580 (p : Pattern) (ha : d269856 p = 1) (hb : d270796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269543 q = 1) (hb : d270554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269543, d270554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269543, d270554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68531 q ha hb
  have h2 (q : Pattern) (ha : d269544 q = 1) (hb : d270555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269544, d270555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269544, d270555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269553 q = 1) (hb : d270564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269553, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68531 q ha hb
    | true =>
      simp only [d269553, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68534 q ha hb
  have h4 (q : Pattern) (ha : d269554 q = 1) (hb : d270565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269554, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269554, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269555 q = 1) (hb : d270566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269555, d270566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269555, d270566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269656 q = 1) (hb : d270652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269656, d270652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68550 q ha hb
    | true =>
      simp only [d269656, d270652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68558 q ha hb
  have h7 (q : Pattern) (ha : d269674 q = 1) (hb : d270670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269674, d270670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68559 q ha hb
    | true =>
      simp only [d269674, d270670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68560 q ha hb
  have h8 (q : Pattern) (ha : d269675 q = 1) (hb : d270671 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269675, d270671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269675, d270671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269676 q = 1) (hb : d270672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269676, d270672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269676, d270672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269677 q = 1) (hb : d270673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269677, d270673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269677, d270673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269681 q = 1) (hb : d270677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269681, d270677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269681, d270677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68561 q ha hb
  have h12 (q : Pattern) (ha : d269683 q = 1) (hb : d270679 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269683, d270679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269683, d270679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68562 q ha hb
  have h13 (q : Pattern) (ha : d269684 q = 1) (hb : d270680 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269684, d270680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269684, d270680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269685 q = 1) (hb : d270681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269685, d270681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269685, d270681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269686 q = 1) (hb : d270682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269686, d270682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269686, d270682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269687 q = 1) (hb : d270683 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269687, d270683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269687, d270683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269840 q = 1) (hb : d270780 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269840, d270780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269840, d270780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68577 q ha hb
  have h18 (q : Pattern) (ha : d269851 q = 1) (hb : d270791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269851, d270791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269851, d270791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68579 q ha hb
  have h19 (q : Pattern) (ha : d269852 q = 1) (hb : d270792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269852, d270792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269852, d270792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d269853 q = 1) (hb : d270793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269853, d270793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269853, d270793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d269854 q = 1) (hb : d270794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269854, d270794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269854, d270794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d269855 q = 1) (hb : d270795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269855, d270795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269855, d270795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d269856 q = 1) (hb : d270796 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269856, d270796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269856, d270796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro68581 (p : Pattern) (ha : d269862 p = 1) (hb : d270802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269857 q = 1) (hb : d270797 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269857, d270797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269857, d270797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68580 q ha hb
  have h2 (q : Pattern) (ha : d269858 q = 1) (hb : d270798 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269858, d270798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269858, d270798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269859 q = 1) (hb : d270799 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269859, d270799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269859, d270799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269860 q = 1) (hb : d270800 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269860, d270800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269860, d270800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269861 q = 1) (hb : d270801 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269861, d270801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269861, d270801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269862 q = 1) (hb : d270802 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269862, d270802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269862, d270802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68582 (p : Pattern) (ha : d269868 p = 1) (hb : d270808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268313 q = 1) (hb : d270027 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268313, d270027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68277 q ha hb
    | true =>
      simp only [d268313, d270027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68323 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268585 q = 1) (hb : d270067 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268585, d270067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268585, d270067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68376 q ha hb
  have h3 (q : Pattern) (ha : d268586 q = 1) (hb : d270068 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268586, d270068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d268586, d270068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268956 q = 1) (hb : d270108 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268956, d270108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268956, d270108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68438 q ha hb
  have h5 (q : Pattern) (ha : d268957 q = 1) (hb : d270109 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268957, d270109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268957, d270109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268958 q = 1) (hb : d270110 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d268958, d270110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268958, d270110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269422 q = 1) (hb : d270467 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269422, d270467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269422, d270467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68513 q ha hb
  have h8 (q : Pattern) (ha : d269423 q = 1) (hb : d270468 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269423, d270468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269423, d270468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269424 q = 1) (hb : d270469 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269424, d270469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269424, d270469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269425 q = 1) (hb : d270470 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269425, d270470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269425, d270470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269863 q = 1) (hb : d270803 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269863, d270803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269863, d270803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68581 q ha hb
  have h12 (q : Pattern) (ha : d269864 q = 1) (hb : d270804 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269864, d270804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269864, d270804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269865 q = 1) (hb : d270805 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269865, d270805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269865, d270805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269866 q = 1) (hb : d270806 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269866, d270806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269866, d270806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269867 q = 1) (hb : d270807 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d269867, d270807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269867, d270807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269868 q = 1) (hb : d270808 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d269868, d270808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269868, d270808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro68583 (p : Pattern) (ha : d269874 p = 1) (hb : d270814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269869 q = 1) (hb : d270809 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d269869, d270809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68582 q ha hb
    | true =>
      simp only [d269869, d270809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269870 q = 1) (hb : d270810 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d269870, d270810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269870, d270810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269871 q = 1) (hb : d270811 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d269871, d270811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269871, d270811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269872 q = 1) (hb : d270812 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d269872, d270812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269872, d270812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269873 q = 1) (hb : d270813 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d269873, d270813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269873, d270813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269874 q = 1) (hb : d270814 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d269874, d270814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269874, d270814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68584 (p : Pattern) (ha : d269880 p = 1) (hb : d270820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269875 q = 1) (hb : d270815 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d269875, d270815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68583 q ha hb
    | true =>
      simp only [d269875, d270815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269876 q = 1) (hb : d270816 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d269876, d270816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269876, d270816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269877 q = 1) (hb : d270817 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d269877, d270817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269877, d270817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269878 q = 1) (hb : d270818 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d269878, d270818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269878, d270818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269879 q = 1) (hb : d270819 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d269879, d270819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269879, d270819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269880 q = 1) (hb : d270820 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d269880, d270820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269880, d270820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68585 (p : Pattern) (ha : d269886 p = 1) (hb : d270826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269881 q = 1) (hb : d270821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d269881, d270821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68584 q ha hb
    | true =>
      simp only [d269881, d270821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269882 q = 1) (hb : d270822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d269882, d270822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269882, d270822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269883 q = 1) (hb : d270823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d269883, d270823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269883, d270823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269884 q = 1) (hb : d270824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d269884, d270824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269884, d270824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269885 q = 1) (hb : d270825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d269885, d270825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269885, d270825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269886 q = 1) (hb : d270826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d269886, d270826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269886, d270826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68586 (p : Pattern) (ha : d269892 p = 1) (hb : d270832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269887 q = 1) (hb : d270827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d269887, d270827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68585 q ha hb
    | true =>
      simp only [d269887, d270827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269888 q = 1) (hb : d270828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d269888, d270828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269888, d270828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269889 q = 1) (hb : d270829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d269889, d270829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269889, d270829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269890 q = 1) (hb : d270830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d269890, d270830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269890, d270830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269891 q = 1) (hb : d270831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d269891, d270831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269891, d270831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269892 q = 1) (hb : d270832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d269892, d270832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269892, d270832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68587 (p : Pattern) (ha : d269898 p = 1) (hb : d270838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269893 q = 1) (hb : d270833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d269893, d270833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68586 q ha hb
    | true =>
      simp only [d269893, d270833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269894 q = 1) (hb : d270834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d269894, d270834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269894, d270834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269895 q = 1) (hb : d270835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d269895, d270835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269895, d270835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269896 q = 1) (hb : d270836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d269896, d270836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269896, d270836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269897 q = 1) (hb : d270837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d269897, d270837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269897, d270837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269898 q = 1) (hb : d270838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d269898, d270838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269898, d270838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68588 (p : Pattern) (ha : d269904 p = 1) (hb : d270844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269899 q = 1) (hb : d270839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d269899, d270839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68587 q ha hb
    | true =>
      simp only [d269899, d270839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269900 q = 1) (hb : d270840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d269900, d270840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269900, d270840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269901 q = 1) (hb : d270841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d269901, d270841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269901, d270841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269902 q = 1) (hb : d270842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d269902, d270842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269902, d270842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269903 q = 1) (hb : d270843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d269903, d270843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269903, d270843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269904 q = 1) (hb : d270844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d269904, d270844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269904, d270844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68589 (p : Pattern) (ha : d269910 p = 1) (hb : d270850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269905 q = 1) (hb : d270845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d269905, d270845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68588 q ha hb
    | true =>
      simp only [d269905, d270845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269906 q = 1) (hb : d270846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d269906, d270846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269906, d270846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269907 q = 1) (hb : d270847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d269907, d270847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269907, d270847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269908 q = 1) (hb : d270848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d269908, d270848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269908, d270848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269909 q = 1) (hb : d270849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d269909, d270849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269909, d270849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269910 q = 1) (hb : d270850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d269910, d270850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269910, d270850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68590 (p : Pattern) (ha : d53655 p = 1) (hb : d267844 p = 1) : d270853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d267844 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d267844 q = 1) : d36033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67873 q ha hb
    | true =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d267844 q = 1) : d36093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d36093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d36093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d267844 q = 1) : d36094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d36094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d36094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d267844 q = 1) : d36095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d36095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d36095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d267844 q = 1) : d36096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d36096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d36096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d267844 q = 1) : d270853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro68591 (p : Pattern) (ha : d53665 p = 1) (hb : d267844 p = 1) : d270863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d267844 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d267844 q = 1) : d36069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d36069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67877 q ha hb
    | true =>
      simp only [d244, d36069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d267844 q = 1) : d270859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d267844 q = 1) : d270860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d267844 q = 1) : d270861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d267844 q = 1) : d270862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d267844 q = 1) : d270863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro68592 (p : Pattern) (ha : d53671 p = 1) (hb : d267844 p = 1) : d270869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d267844 q = 1) : d36098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d36098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67883 q ha hb
    | true =>
      simp only [d292, d36098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67884 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d267844 q = 1) : d36099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d36099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d36099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d267844 q = 1) : d270851 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d267844 q = 1) : d270852 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d267844 q = 1) : d270854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68590 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d267844 q = 1) : d270855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d267844 q = 1) : d270856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d267844 q = 1) : d270857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d267844 q = 1) : d270858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d267844 q = 1) : d270864 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68591 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d267844 q = 1) : d270865 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d267844 q = 1) : d270866 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d267844 q = 1) : d270867 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d267844 q = 1) : d270868 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d267844 q = 1) : d270869 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68593 (p : Pattern) (ha : d53677 p = 1) (hb : d267844 p = 1) : d270875 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d267844 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d267844 q = 1) : d270870 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68592 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d267844 q = 1) : d270871 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d267844 q = 1) : d270872 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d267844 q = 1) : d270873 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d267844 q = 1) : d270874 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d267844 q = 1) : d270875 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro68594 (p : Pattern) (ha : d171078 p = 1) (hb : d267844 p = 1) : d270878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d267844 q = 1) : d36307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d36307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67920 q ha hb
    | true =>
      simp only [d16052, d36307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67911 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d267844 q = 1) : d36308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d36308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d36308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d267844 q = 1) : d36309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d36309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d36309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d267844 q = 1) : d36310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d36310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d36310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d267844 q = 1) : d36311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d36311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d36311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171078 q = 1) (hb : d267844 q = 1) : d270878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171078, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68595 (p : Pattern) (ha : d171089 p = 1) (hb : d267844 p = 1) : d270889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171084 q = 1) (hb : d267844 q = 1) : d270884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d270884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67951 q ha hb
    | true =>
      simp only [d171084, d270884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67915 q ha hb
  have h2 (q : Pattern) (ha : d171085 q = 1) (hb : d267844 q = 1) : d270885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171085, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171086 q = 1) (hb : d267844 q = 1) : d270886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171087 q = 1) (hb : d267844 q = 1) : d270887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171087, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171088 q = 1) (hb : d267844 q = 1) : d270888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171088, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171089 q = 1) (hb : d267844 q = 1) : d270889 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171089, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68596 (p : Pattern) (ha : d171095 p = 1) (hb : d267844 p = 1) : d270895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d267844 q = 1) : d36313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d36313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67919 q ha hb
    | true =>
      simp only [d16058, d36313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67921 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d267844 q = 1) : d36314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d36314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d36314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171076 q = 1) (hb : d267844 q = 1) : d270876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171076, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171077 q = 1) (hb : d267844 q = 1) : d270877 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171077, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171079 q = 1) (hb : d267844 q = 1) : d270879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171079, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68594 q ha hb
  have h6 (q : Pattern) (ha : d171080 q = 1) (hb : d267844 q = 1) : d270880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171081 q = 1) (hb : d267844 q = 1) : d270881 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171082 q = 1) (hb : d267844 q = 1) : d270882 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171083 q = 1) (hb : d267844 q = 1) : d270883 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171090 q = 1) (hb : d267844 q = 1) : d270890 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171090, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68595 q ha hb
  have h11 (q : Pattern) (ha : d171091 q = 1) (hb : d267844 q = 1) : d270891 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171092 q = 1) (hb : d267844 q = 1) : d270892 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171093 q = 1) (hb : d267844 q = 1) : d270893 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171094 q = 1) (hb : d267844 q = 1) : d270894 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171095 q = 1) (hb : d267844 q = 1) : d270895 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68597 (p : Pattern) (ha : d171101 p = 1) (hb : d267844 p = 1) : d270901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171096 q = 1) (hb : d267844 q = 1) : d270896 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171096, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68596 q ha hb
  have h2 (q : Pattern) (ha : d171097 q = 1) (hb : d267844 q = 1) : d270897 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171097, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171098 q = 1) (hb : d267844 q = 1) : d270898 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171098, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171099 q = 1) (hb : d267844 q = 1) : d270899 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171099, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171100 q = 1) (hb : d267844 q = 1) : d270900 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171100, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171101 q = 1) (hb : d267844 q = 1) : d270901 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171101, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68598 (p : Pattern) (ha : d171105 p = 1) (hb : d267844 p = 1) : d270905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d267844 q = 1) : d36639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d36639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67973 q ha hb
    | true =>
      simp only [d16249, d36639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67961 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d267844 q = 1) : d36640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d36640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d36640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d267844 q = 1) : d36641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d36641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d36641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d267844 q = 1) : d36642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d36642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d36642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d267844 q = 1) : d36643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d36643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d36643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171105 q = 1) (hb : d267844 q = 1) : d270905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171105, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68599 (p : Pattern) (ha : d171116 p = 1) (hb : d267844 p = 1) : d270916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171111 q = 1) (hb : d267844 q = 1) : d270911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d270911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68005 q ha hb
    | true =>
      simp only [d171111, d270911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67967 q ha hb
  have h2 (q : Pattern) (ha : d171112 q = 1) (hb : d267844 q = 1) : d270912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171112, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171113 q = 1) (hb : d267844 q = 1) : d270913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171114 q = 1) (hb : d267844 q = 1) : d270914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171114, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171115 q = 1) (hb : d267844 q = 1) : d270915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171115, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171116 q = 1) (hb : d267844 q = 1) : d270916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171116, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68600 (p : Pattern) (ha : d171122 p = 1) (hb : d267844 p = 1) : d270922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d267844 q = 1) : d36645 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d36645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67972 q ha hb
    | true =>
      simp only [d16255, d36645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67974 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d267844 q = 1) : d36646 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d36646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d36646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171103 q = 1) (hb : d267844 q = 1) : d270903 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171103, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171104 q = 1) (hb : d267844 q = 1) : d270904 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171104, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171106 q = 1) (hb : d267844 q = 1) : d270906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171106, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68598 q ha hb
  have h6 (q : Pattern) (ha : d171107 q = 1) (hb : d267844 q = 1) : d270907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171108 q = 1) (hb : d267844 q = 1) : d270908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171109 q = 1) (hb : d267844 q = 1) : d270909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171110 q = 1) (hb : d267844 q = 1) : d270910 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171117 q = 1) (hb : d267844 q = 1) : d270917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171117, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68599 q ha hb
  have h11 (q : Pattern) (ha : d171118 q = 1) (hb : d267844 q = 1) : d270918 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171119 q = 1) (hb : d267844 q = 1) : d270919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171120 q = 1) (hb : d267844 q = 1) : d270920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171121 q = 1) (hb : d267844 q = 1) : d270921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171122 q = 1) (hb : d267844 q = 1) : d270922 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68601 (p : Pattern) (ha : d171128 p = 1) (hb : d267844 p = 1) : d270928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171123 q = 1) (hb : d267844 q = 1) : d270923 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171123, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68600 q ha hb
  have h2 (q : Pattern) (ha : d171124 q = 1) (hb : d267844 q = 1) : d270924 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171124, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171125 q = 1) (hb : d267844 q = 1) : d270925 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171125, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171126 q = 1) (hb : d267844 q = 1) : d270926 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171126, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171127 q = 1) (hb : d267844 q = 1) : d270927 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171127, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171128 q = 1) (hb : d267844 q = 1) : d270928 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171128, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68602 (p : Pattern) (ha : d171133 p = 1) (hb : d267844 p = 1) : d270933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d267844 q = 1) : d37070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d37070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68026 q ha hb
    | true =>
      simp only [d16481, d37070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68027 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d267844 q = 1) : d37071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d37071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d37071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d267844 q = 1) : d37072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d37072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d37072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d267844 q = 1) : d37073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d37073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d37073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d267844 q = 1) : d37074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d37074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d37074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171133 q = 1) (hb : d267844 q = 1) : d270933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171133, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68603 (p : Pattern) (ha : d171140 p = 1) (hb : d267844 p = 1) : d37376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d267844 q = 1) : d37361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d37361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68068 q ha hb
    | true =>
      simp only [d16673, d37361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68035 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d267844 q = 1) : d37362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d37362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d37362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d267844 q = 1) : d37363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d37363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d37363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d267844 q = 1) : d37366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d37366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68035 q ha hb
    | true =>
      simp only [d16676, d37366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68066 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d267844 q = 1) : d37367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d37367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d37367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d267844 q = 1) : d37368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d37368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d37368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d267844 q = 1) : d37369 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d37369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d37369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d267844 q = 1) : d37366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d37366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68035 q ha hb
    | true =>
      simp only [d16693, d37366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68034 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d267844 q = 1) : d37367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d37367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d37367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d267844 q = 1) : d37368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d37368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d37368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d267844 q = 1) : d37374 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d37374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d37374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171139 q = 1) (hb : d267844 q = 1) : d37375 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d37375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171139, d37375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171140 q = 1) (hb : d267844 q = 1) : d37376 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d37376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d37376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro68604 (p : Pattern) (ha : d171146 p = 1) (hb : d267844 p = 1) : d37390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171141 q = 1) (hb : d267844 q = 1) : d37377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d37377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68603 q ha hb
    | true =>
      simp only [d171141, d37377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d171142 q = 1) (hb : d267844 q = 1) : d37378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d37378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171142, d37378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d267844 q = 1) : d37385 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d37385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68036 q ha hb
    | true =>
      simp only [d16699, d37385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d267844 q = 1) : d37386 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d37386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d37386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171143 q = 1) (hb : d267844 q = 1) : d37387 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d37387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d37387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171144 q = 1) (hb : d267844 q = 1) : d37388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d37388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d37388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171145 q = 1) (hb : d267844 q = 1) : d37389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d37389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d37389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171146 q = 1) (hb : d267844 q = 1) : d37390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d37390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d37390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro68605 (p : Pattern) (ha : d171152 p = 1) (hb : d267844 p = 1) : d270944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171147 q = 1) (hb : d267844 q = 1) : d270939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d270939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68604 q ha hb
    | true =>
      simp only [d171147, d270939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68037 q ha hb
  have h2 (q : Pattern) (ha : d171148 q = 1) (hb : d267844 q = 1) : d270940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171148, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171149 q = 1) (hb : d267844 q = 1) : d270941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171150 q = 1) (hb : d267844 q = 1) : d270942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171150, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171151 q = 1) (hb : d267844 q = 1) : d270943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171151, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171152 q = 1) (hb : d267844 q = 1) : d270944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171152, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68606 (p : Pattern) (ha : d171158 p = 1) (hb : d267844 p = 1) : d270950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d267844 q = 1) : d37076 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d37076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68025 q ha hb
    | true =>
      simp only [d16487, d37076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68028 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d267844 q = 1) : d37077 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d37077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d37077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171131 q = 1) (hb : d267844 q = 1) : d270931 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171131, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d171132 q = 1) (hb : d267844 q = 1) : d270932 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171132, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171134 q = 1) (hb : d267844 q = 1) : d270934 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171134, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68602 q ha hb
  have h6 (q : Pattern) (ha : d171135 q = 1) (hb : d267844 q = 1) : d270935 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d171136 q = 1) (hb : d267844 q = 1) : d270936 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d171137 q = 1) (hb : d267844 q = 1) : d270937 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d171138 q = 1) (hb : d267844 q = 1) : d270938 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171153 q = 1) (hb : d267844 q = 1) : d270945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171153, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68605 q ha hb
  have h11 (q : Pattern) (ha : d171154 q = 1) (hb : d267844 q = 1) : d270946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171155 q = 1) (hb : d267844 q = 1) : d270947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d171156 q = 1) (hb : d267844 q = 1) : d270948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d171157 q = 1) (hb : d267844 q = 1) : d270949 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d171158 q = 1) (hb : d267844 q = 1) : d270950 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68607 (p : Pattern) (ha : d171164 p = 1) (hb : d267844 p = 1) : d270956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171159 q = 1) (hb : d267844 q = 1) : d270951 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171159, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68606 q ha hb
  have h2 (q : Pattern) (ha : d171160 q = 1) (hb : d267844 q = 1) : d270952 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171160, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171161 q = 1) (hb : d267844 q = 1) : d270953 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171161, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171162 q = 1) (hb : d267844 q = 1) : d270954 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171162, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171163 q = 1) (hb : d267844 q = 1) : d270955 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171163, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171164 q = 1) (hb : d267844 q = 1) : d270956 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171164, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68608 (p : Pattern) (ha : d212441 p = 1) (hb : d267844 p = 1) : d270962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27604 q = 1) (hb : d267844 q = 1) : d270203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27604, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68105 q ha hb
    | true =>
      simp only [d27604, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68106 q ha hb
  have h2 (q : Pattern) (ha : d27605 q = 1) (hb : d267844 q = 1) : d270204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27605, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27606 q = 1) (hb : d267844 q = 1) : d270205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27606, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27607 q = 1) (hb : d267844 q = 1) : d270206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27607, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27608 q = 1) (hb : d267844 q = 1) : d270207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27608, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212441 q = 1) (hb : d267844 q = 1) : d270962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212441, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212441, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68609 (p : Pattern) (ha : d212448 p = 1) (hb : d267844 p = 1) : d270969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27923 q = 1) (hb : d267844 q = 1) : d270378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68144 q ha hb
    | true =>
      simp only [d27923, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68113 q ha hb
  have h2 (q : Pattern) (ha : d27924 q = 1) (hb : d267844 q = 1) : d270379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27925 q = 1) (hb : d267844 q = 1) : d270380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27937 q = 1) (hb : d267844 q = 1) : d270392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68113 q ha hb
    | true =>
      simp only [d27937, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68146 q ha hb
  have h5 (q : Pattern) (ha : d27938 q = 1) (hb : d267844 q = 1) : d270393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27939 q = 1) (hb : d267844 q = 1) : d270394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27940 q = 1) (hb : d267844 q = 1) : d270395 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27940, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27960 q = 1) (hb : d267844 q = 1) : d270411 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27960, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68113 q ha hb
    | true =>
      simp only [d27960, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68114 q ha hb
  have h9 (q : Pattern) (ha : d27961 q = 1) (hb : d267844 q = 1) : d270412 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27961, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27961, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27962 q = 1) (hb : d267844 q = 1) : d270413 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27962, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27962, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27963 q = 1) (hb : d267844 q = 1) : d270414 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27963, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27963, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212447 q = 1) (hb : d267844 q = 1) : d270968 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212447, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212447, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212448 q = 1) (hb : d267844 q = 1) : d270969 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212448, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212448, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro68610 (p : Pattern) (ha : d212454 p = 1) (hb : d267844 p = 1) : d270975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212449 q = 1) (hb : d267844 q = 1) : d270970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212449, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68609 q ha hb
    | true =>
      simp only [d212449, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212450 q = 1) (hb : d267844 q = 1) : d270971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212450, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212450, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27966 q = 1) (hb : d267844 q = 1) : d270417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27966, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68115 q ha hb
    | true =>
      simp only [d27966, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27967 q = 1) (hb : d267844 q = 1) : d270418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27967, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27967, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212451 q = 1) (hb : d267844 q = 1) : d270972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212451, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212451, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212452 q = 1) (hb : d267844 q = 1) : d270973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212452, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212452, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212453 q = 1) (hb : d267844 q = 1) : d270974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212453, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212453, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212454 q = 1) (hb : d267844 q = 1) : d270975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212454, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212454, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro68611 (p : Pattern) (ha : d212460 p = 1) (hb : d267844 p = 1) : d270981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212455 q = 1) (hb : d267844 q = 1) : d270976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212455, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68610 q ha hb
    | true =>
      simp only [d212455, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68116 q ha hb
  have h2 (q : Pattern) (ha : d212456 q = 1) (hb : d267844 q = 1) : d270977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212456, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212456, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212457 q = 1) (hb : d267844 q = 1) : d270978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212457, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212457, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212458 q = 1) (hb : d267844 q = 1) : d270979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212458, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212458, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212459 q = 1) (hb : d267844 q = 1) : d270980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212459, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212459, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212460 q = 1) (hb : d267844 q = 1) : d270981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212460, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212460, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68612 (p : Pattern) (ha : d212466 p = 1) (hb : d267844 p = 1) : d270987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27610 q = 1) (hb : d267844 q = 1) : d270209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27610, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68104 q ha hb
    | true =>
      simp only [d27610, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68107 q ha hb
  have h2 (q : Pattern) (ha : d27611 q = 1) (hb : d267844 q = 1) : d270210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27611, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27611, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212439 q = 1) (hb : d267844 q = 1) : d270960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212439, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212439, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212440 q = 1) (hb : d267844 q = 1) : d270961 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212440, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212440, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212442 q = 1) (hb : d267844 q = 1) : d270963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212442, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212442, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68608 q ha hb
  have h6 (q : Pattern) (ha : d212443 q = 1) (hb : d267844 q = 1) : d270964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212443, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212443, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212444 q = 1) (hb : d267844 q = 1) : d270965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212444, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212444, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212445 q = 1) (hb : d267844 q = 1) : d270966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212445, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212445, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d212446 q = 1) (hb : d267844 q = 1) : d270967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212446, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212446, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212461 q = 1) (hb : d267844 q = 1) : d270982 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212461, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212461, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68611 q ha hb
  have h11 (q : Pattern) (ha : d212462 q = 1) (hb : d267844 q = 1) : d270983 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212462, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212462, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212463 q = 1) (hb : d267844 q = 1) : d270984 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212463, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212463, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d212464 q = 1) (hb : d267844 q = 1) : d270985 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212464, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212464, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d212465 q = 1) (hb : d267844 q = 1) : d270986 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212465, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212465, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d212466 q = 1) (hb : d267844 q = 1) : d270987 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212466, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212466, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68613 (p : Pattern) (ha : d212472 p = 1) (hb : d267844 p = 1) : d270993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212467 q = 1) (hb : d267844 q = 1) : d270988 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212467, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212467, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68612 q ha hb
  have h2 (q : Pattern) (ha : d212468 q = 1) (hb : d267844 q = 1) : d270989 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212468, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212468, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212469 q = 1) (hb : d267844 q = 1) : d270990 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212469, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212469, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212470 q = 1) (hb : d267844 q = 1) : d270991 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212470, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212470, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212471 q = 1) (hb : d267844 q = 1) : d270992 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212471, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212471, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212472 q = 1) (hb : d267844 q = 1) : d270993 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212472, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212472, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68614 (p : Pattern) (ha : d212479 p = 1) (hb : d267844 p = 1) : d271000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28218 q = 1) (hb : d267844 q = 1) : d270558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28218, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68181 q ha hb
    | true =>
      simp only [d28218, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68182 q ha hb
  have h2 (q : Pattern) (ha : d28219 q = 1) (hb : d267844 q = 1) : d270559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28219, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28220 q = 1) (hb : d267844 q = 1) : d270560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28220, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28221 q = 1) (hb : d267844 q = 1) : d270561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28221, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28222 q = 1) (hb : d267844 q = 1) : d270562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28222, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212479 q = 1) (hb : d267844 q = 1) : d271000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212479, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212479, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68615 (p : Pattern) (ha : d212486 p = 1) (hb : d267844 p = 1) : d271007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28523 q = 1) (hb : d267844 q = 1) : d270714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68218 q ha hb
    | true =>
      simp only [d28523, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68189 q ha hb
  have h2 (q : Pattern) (ha : d28524 q = 1) (hb : d267844 q = 1) : d270715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28525 q = 1) (hb : d267844 q = 1) : d270716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28537 q = 1) (hb : d267844 q = 1) : d270728 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68189 q ha hb
    | true =>
      simp only [d28537, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68220 q ha hb
  have h5 (q : Pattern) (ha : d28538 q = 1) (hb : d267844 q = 1) : d270729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28539 q = 1) (hb : d267844 q = 1) : d270730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28540 q = 1) (hb : d267844 q = 1) : d270731 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28540, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28560 q = 1) (hb : d267844 q = 1) : d270747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28560, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68189 q ha hb
    | true =>
      simp only [d28560, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68190 q ha hb
  have h9 (q : Pattern) (ha : d28561 q = 1) (hb : d267844 q = 1) : d270748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28561, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28561, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28562 q = 1) (hb : d267844 q = 1) : d270749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28562, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28562, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28563 q = 1) (hb : d267844 q = 1) : d270750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28563, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28563, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212485 q = 1) (hb : d267844 q = 1) : d271006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212485, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212485, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212486 q = 1) (hb : d267844 q = 1) : d271007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212486, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212486, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro68616 (p : Pattern) (ha : d212492 p = 1) (hb : d267844 p = 1) : d271013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212487 q = 1) (hb : d267844 q = 1) : d271008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212487, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68615 q ha hb
    | true =>
      simp only [d212487, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212488 q = 1) (hb : d267844 q = 1) : d271009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212488, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212488, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28566 q = 1) (hb : d267844 q = 1) : d270753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28566, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68191 q ha hb
    | true =>
      simp only [d28566, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28567 q = 1) (hb : d267844 q = 1) : d270754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28567, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28567, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212489 q = 1) (hb : d267844 q = 1) : d271010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212489, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212489, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212490 q = 1) (hb : d267844 q = 1) : d271011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212490, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212490, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212491 q = 1) (hb : d267844 q = 1) : d271012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212491, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212491, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212492 q = 1) (hb : d267844 q = 1) : d271013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212492, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212492, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro68617 (p : Pattern) (ha : d212498 p = 1) (hb : d267844 p = 1) : d271019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212493 q = 1) (hb : d267844 q = 1) : d271014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212493, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68616 q ha hb
    | true =>
      simp only [d212493, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68192 q ha hb
  have h2 (q : Pattern) (ha : d212494 q = 1) (hb : d267844 q = 1) : d271015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212494, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212494, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212495 q = 1) (hb : d267844 q = 1) : d271016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212495, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212495, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212496 q = 1) (hb : d267844 q = 1) : d271017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212496, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212496, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212497 q = 1) (hb : d267844 q = 1) : d271018 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212497, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212497, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212498 q = 1) (hb : d267844 q = 1) : d271019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212498, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212498, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68618 (p : Pattern) (ha : d212504 p = 1) (hb : d267844 p = 1) : d271025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28224 q = 1) (hb : d267844 q = 1) : d270564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28224, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68180 q ha hb
    | true =>
      simp only [d28224, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68183 q ha hb
  have h2 (q : Pattern) (ha : d28225 q = 1) (hb : d267844 q = 1) : d270565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28225, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28225, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212477 q = 1) (hb : d267844 q = 1) : d270998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212477, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212477, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212478 q = 1) (hb : d267844 q = 1) : d270999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212478, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212478, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212480 q = 1) (hb : d267844 q = 1) : d271001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212480, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212480, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68614 q ha hb
  have h6 (q : Pattern) (ha : d212481 q = 1) (hb : d267844 q = 1) : d271002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212481, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212481, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d212482 q = 1) (hb : d267844 q = 1) : d271003 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212482, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212482, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d212483 q = 1) (hb : d267844 q = 1) : d271004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212483, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212483, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d212484 q = 1) (hb : d267844 q = 1) : d271005 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212484, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212484, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212499 q = 1) (hb : d267844 q = 1) : d271020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212499, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212499, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68617 q ha hb
  have h11 (q : Pattern) (ha : d212500 q = 1) (hb : d267844 q = 1) : d271021 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212500, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212500, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d212501 q = 1) (hb : d267844 q = 1) : d271022 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212501, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212501, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d212502 q = 1) (hb : d267844 q = 1) : d271023 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212502, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212502, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d212503 q = 1) (hb : d267844 q = 1) : d271024 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212503, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212503, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d212504 q = 1) (hb : d267844 q = 1) : d271025 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212504, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212504, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro68619 (p : Pattern) (ha : d212510 p = 1) (hb : d267844 p = 1) : d271031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212505 q = 1) (hb : d267844 q = 1) : d271026 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212505, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212505, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68618 q ha hb
  have h2 (q : Pattern) (ha : d212506 q = 1) (hb : d267844 q = 1) : d271027 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212506, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212506, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212507 q = 1) (hb : d267844 q = 1) : d271028 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212507, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212507, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212508 q = 1) (hb : d267844 q = 1) : d271029 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212508, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212508, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212509 q = 1) (hb : d267844 q = 1) : d271030 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212509, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212509, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212510 q = 1) (hb : d267844 q = 1) : d271031 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212510, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212510, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68620 (p : Pattern) (ha : d212516 p = 1) (hb : d267844 p = 1) : d271037 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d267844 q = 1) : d270902 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68593 q ha hb
    | true =>
      simp only [d171102, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68597 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171129 q = 1) (hb : d267844 q = 1) : d270929 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171129, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68601 q ha hb
  have h3 (q : Pattern) (ha : d171130 q = 1) (hb : d267844 q = 1) : d270930 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171165 q = 1) (hb : d267844 q = 1) : d270957 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171165, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68607 q ha hb
  have h5 (q : Pattern) (ha : d171166 q = 1) (hb : d267844 q = 1) : d270958 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171166, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171167 q = 1) (hb : d267844 q = 1) : d270959 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212473 q = 1) (hb : d267844 q = 1) : d270994 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212473, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212473, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68613 q ha hb
  have h8 (q : Pattern) (ha : d212474 q = 1) (hb : d267844 q = 1) : d270995 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212474, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212474, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212475 q = 1) (hb : d267844 q = 1) : d270996 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212475, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212475, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212476 q = 1) (hb : d267844 q = 1) : d270997 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212476, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212476, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212511 q = 1) (hb : d267844 q = 1) : d271032 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212511, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212511, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68619 q ha hb
  have h12 (q : Pattern) (ha : d212512 q = 1) (hb : d267844 q = 1) : d271033 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212512, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212512, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212513 q = 1) (hb : d267844 q = 1) : d271034 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212513, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212513, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d212514 q = 1) (hb : d267844 q = 1) : d271035 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212514, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212514, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d212515 q = 1) (hb : d267844 q = 1) : d271036 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212515, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212515, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d212516 q = 1) (hb : d267844 q = 1) : d271037 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212516, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212516, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro68621 (p : Pattern) (ha : d212522 p = 1) (hb : d267844 p = 1) : d271043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212517 q = 1) (hb : d267844 q = 1) : d271038 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212517, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68620 q ha hb
    | true =>
      simp only [d212517, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212518 q = 1) (hb : d267844 q = 1) : d271039 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212518, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212518, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212519 q = 1) (hb : d267844 q = 1) : d271040 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212519, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212519, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212520 q = 1) (hb : d267844 q = 1) : d271041 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212520, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212520, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212521 q = 1) (hb : d267844 q = 1) : d271042 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212521, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212521, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212522 q = 1) (hb : d267844 q = 1) : d271043 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212522, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212522, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68622 (p : Pattern) (ha : d212528 p = 1) (hb : d267844 p = 1) : d271049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212523 q = 1) (hb : d267844 q = 1) : d271044 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212523, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68621 q ha hb
    | true =>
      simp only [d212523, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212524 q = 1) (hb : d267844 q = 1) : d271045 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212524, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212524, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212525 q = 1) (hb : d267844 q = 1) : d271046 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212525, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212525, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212526 q = 1) (hb : d267844 q = 1) : d271047 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212526, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212526, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212527 q = 1) (hb : d267844 q = 1) : d271048 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212527, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212527, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212528 q = 1) (hb : d267844 q = 1) : d271049 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212528, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212528, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68623 (p : Pattern) (ha : d212534 p = 1) (hb : d267844 p = 1) : d271055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212529 q = 1) (hb : d267844 q = 1) : d271050 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212529, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68622 q ha hb
    | true =>
      simp only [d212529, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212530 q = 1) (hb : d267844 q = 1) : d271051 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212530, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212530, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212531 q = 1) (hb : d267844 q = 1) : d271052 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212531, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212531, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212532 q = 1) (hb : d267844 q = 1) : d271053 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212532, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212532, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212533 q = 1) (hb : d267844 q = 1) : d271054 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212533, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212533, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212534 q = 1) (hb : d267844 q = 1) : d271055 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212534, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212534, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68624 (p : Pattern) (ha : d212540 p = 1) (hb : d267844 p = 1) : d271061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212535 q = 1) (hb : d267844 q = 1) : d271056 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212535, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68623 q ha hb
    | true =>
      simp only [d212535, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212536 q = 1) (hb : d267844 q = 1) : d271057 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212536, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212536, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212537 q = 1) (hb : d267844 q = 1) : d271058 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212537, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212537, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212538 q = 1) (hb : d267844 q = 1) : d271059 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212538, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212538, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212539 q = 1) (hb : d267844 q = 1) : d271060 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212539, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212539, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212540 q = 1) (hb : d267844 q = 1) : d271061 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212540, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212540, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68625 (p : Pattern) (ha : d212546 p = 1) (hb : d267844 p = 1) : d271067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212541 q = 1) (hb : d267844 q = 1) : d271062 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212541, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68624 q ha hb
    | true =>
      simp only [d212541, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212542 q = 1) (hb : d267844 q = 1) : d271063 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212542, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212542, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212543 q = 1) (hb : d267844 q = 1) : d271064 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212543, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212543, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212544 q = 1) (hb : d267844 q = 1) : d271065 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212544, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212544, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212545 q = 1) (hb : d267844 q = 1) : d271066 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212545, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212545, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212546 q = 1) (hb : d267844 q = 1) : d271067 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212546, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212546, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68626 (p : Pattern) (ha : d212552 p = 1) (hb : d267844 p = 1) : d271073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212547 q = 1) (hb : d267844 q = 1) : d271068 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212547, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68625 q ha hb
    | true =>
      simp only [d212547, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212548 q = 1) (hb : d267844 q = 1) : d271069 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212548, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212548, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212549 q = 1) (hb : d267844 q = 1) : d271070 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212549, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212549, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212550 q = 1) (hb : d267844 q = 1) : d271071 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212550, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212550, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212551 q = 1) (hb : d267844 q = 1) : d271072 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212551, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212551, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212552 q = 1) (hb : d267844 q = 1) : d271073 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212552, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212552, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68627 (p : Pattern) (ha : d212558 p = 1) (hb : d267844 p = 1) : d271079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212553 q = 1) (hb : d267844 q = 1) : d271074 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212553, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68626 q ha hb
    | true =>
      simp only [d212553, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212554 q = 1) (hb : d267844 q = 1) : d271075 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212554, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212554, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212555 q = 1) (hb : d267844 q = 1) : d271076 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212555, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212555, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212556 q = 1) (hb : d267844 q = 1) : d271077 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212556, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212556, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212557 q = 1) (hb : d267844 q = 1) : d271078 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212557, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212557, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212558 q = 1) (hb : d267844 q = 1) : d271079 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212558, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212558, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68628 (p : Pattern) (ha : d104 p = 1) (hb : d267871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267866 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d267867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d267867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d267867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d267868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d267868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d267868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d267869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d267869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d267869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d267870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d267870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d267870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d267871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d267871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d267871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68629 (p : Pattern) (ha : d111 p = 1) (hb : d267878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267866 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d267867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d267867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d267867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d267868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d267868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d267868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d267869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d267869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d267869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d267870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d267870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d267870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d267873 q = 1) : d0 q = 1 := by
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
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d267874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d267874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d267874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d267875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d267875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d267875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d267876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d267876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d267876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d267877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d267877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d267877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d267878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d267878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d267878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68630 (p : Pattern) (ha : d406 p = 1) (hb : d267885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267873 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d267874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d267874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d267874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d267875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d267875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d267875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d267883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d267883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d267883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d267884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d267884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d267884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d267885 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d267885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d267885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68631 (p : Pattern) (ha : d462 p = 1) (hb : d267914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267909 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d267910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d267910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d267910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d267911 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d267911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d267911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d267912 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d267912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d267912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d267913 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d267913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d267913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d267914 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d267914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d267914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68632 (p : Pattern) (ha : d53647 p = 1) (hb : d267920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d267879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d267879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68628 q ha hb
    | true =>
      simp only [d112, d267879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68629 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d267880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d267880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d267880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d267881 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d267881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d267881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d267882 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d267882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d267882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d267886 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d267886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d267886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68630 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d267887 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d267887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d267887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d267888 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d267888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d267888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d267889 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d267889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d267889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d267890 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d267890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d267890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d267915 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d267915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d267915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68631 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d267916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d267916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d267916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d267917 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d267917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d267917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d267918 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d267918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d267918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d267919 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d267919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d267919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d267920 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d267920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d267920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro68633 (p : Pattern) (ha : d36090 p = 1) (hb : d267996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267952 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267985 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36026 q = 1) (hb : d267866 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d267866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68242 q ha hb
    | true =>
      simp only [d36026, d267866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d36086 q = 1) (hb : d267986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d267986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36086, d267986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d267992 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36087 q = 1) (hb : d267993 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d267993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36087, d267993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36088 q = 1) (hb : d267994 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d267994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36088, d267994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36089 q = 1) (hb : d267995 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d267995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36089, d267995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36090 q = 1) (hb : d267996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36090, d267996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36090, d267996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68634 (p : Pattern) (ha : d36097 p = 1) (hb : d268015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267946 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36026 q = 1) (hb : d267866 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d267866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68242 q ha hb
    | true =>
      simp only [d36026, d267866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d36086 q = 1) (hb : d267986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d267986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36086, d267986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d267992 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36087 q = 1) (hb : d267993 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d267993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36087, d267993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36088 q = 1) (hb : d267994 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d267994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36088, d267994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36089 q = 1) (hb : d267995 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d267995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d267995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268001 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268005 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268007 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36033 q = 1) (hb : d267873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d267873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68244 q ha hb
    | true =>
      simp only [d36033, d267873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d36093 q = 1) (hb : d268008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d268008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36093, d268008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268011 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36094 q = 1) (hb : d268012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d268012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36094, d268012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36095 q = 1) (hb : d268013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d268013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36095, d268013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36096 q = 1) (hb : d268014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d268014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36096, d268014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36097 q = 1) (hb : d268015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36097, d268015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36097, d268015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68635 (p : Pattern) (ha : d268024 p = 1) (hb : d270853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36033 q = 1) (hb : d267873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d267873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68244 q ha hb
    | true =>
      simp only [d36033, d267873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d36093 q = 1) (hb : d268008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d268008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36093, d268008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36094 q = 1) (hb : d268012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d268012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36094, d268012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36095 q = 1) (hb : d268022 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d268022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d268022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36096 q = 1) (hb : d268023 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d268023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d268023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268024 q = 1) (hb : d270853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268024, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268024, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68636 (p : Pattern) (ha : d268064 p = 1) (hb : d270863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36069 q = 1) (hb : d267909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36069, d267909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68249 q ha hb
    | true =>
      simp only [d36069, d267909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d268054 q = 1) (hb : d270859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268054, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268054, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268061 q = 1) (hb : d270860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268061, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268061, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268062 q = 1) (hb : d270861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268062, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268062, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268063 q = 1) (hb : d270862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268063, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268063, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268064 q = 1) (hb : d270863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268064, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268064, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68637 (p : Pattern) (ha : d268070 p = 1) (hb : d270869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267940 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36098 q = 1) (hb : d268016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d268016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68633 q ha hb
    | true =>
      simp only [d36098, d268016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36099 q = 1) (hb : d268019 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d268019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36099, d268019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268020 q = 1) (hb : d270851 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268020, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268020, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268021 q = 1) (hb : d270852 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268021, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268021, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268025 q = 1) (hb : d270854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268025, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268025, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68635 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268026 q = 1) (hb : d270855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268026, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268026, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268027 q = 1) (hb : d270856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268027, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268027, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268028 q = 1) (hb : d270857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268028, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268028, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268029 q = 1) (hb : d270858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268029, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268029, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268065 q = 1) (hb : d270864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268065, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268065, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68636 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268066 q = 1) (hb : d270865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268066, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268066, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268067 q = 1) (hb : d270866 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268067, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268067, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268068 q = 1) (hb : d270867 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268068, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268068, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268069 q = 1) (hb : d270868 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268069, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268069, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268070 q = 1) (hb : d270869 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268070, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268070, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68638 (p : Pattern) (ha : d268076 p = 1) (hb : d270875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d267921 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d267921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d267921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68632 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d267922 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d267922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d267922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d267923 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d267923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d267923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d267924 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d267924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d267924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d267925 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d267925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d267925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268071 q = 1) (hb : d270870 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268071, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268071, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68637 q ha hb
  have h8 (q : Pattern) (ha : d268072 q = 1) (hb : d270871 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268072, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268072, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d268073 q = 1) (hb : d270872 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268073, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268073, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d268074 q = 1) (hb : d270873 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268074, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268074, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d268075 q = 1) (hb : d270874 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268075, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268075, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d268076 q = 1) (hb : d270875 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268076, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d268076, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro68639 (p : Pattern) (ha : d36302 p = 1) (hb : d268184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268173 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36297 q = 1) (hb : d268094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d268094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68280 q ha hb
    | true =>
      simp only [d36297, d268094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68281 q ha hb
  have h5 (q : Pattern) (ha : d36298 q = 1) (hb : d268174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d268174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36298, d268174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268180 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36299 q = 1) (hb : d268181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d268181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36299, d268181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36300 q = 1) (hb : d268182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d268182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36300, d268182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36301 q = 1) (hb : d268183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d268183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36301, d268183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36302 q = 1) (hb : d268184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36302, d268184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36302, d268184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68640 (p : Pattern) (ha : d36312 p = 1) (hb : d268205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36297 q = 1) (hb : d268094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d268094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68280 q ha hb
    | true =>
      simp only [d36297, d268094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68281 q ha hb
  have h4 (q : Pattern) (ha : d36298 q = 1) (hb : d268174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d268174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36298, d268174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268180 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36299 q = 1) (hb : d268181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d268181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36299, d268181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36300 q = 1) (hb : d268182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d268182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36300, d268182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36301 q = 1) (hb : d268183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d268183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d268183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268190 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268195 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268197 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36307 q = 1) (hb : d268104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d268104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68283 q ha hb
    | true =>
      simp only [d36307, d268104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68284 q ha hb
  have h13 (q : Pattern) (ha : d36308 q = 1) (hb : d268198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d268198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36308, d268198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268201 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36309 q = 1) (hb : d268202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d268202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36309, d268202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36310 q = 1) (hb : d268203 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d268203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36310, d268203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36311 q = 1) (hb : d268204 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d268204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36311, d268204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36312 q = 1) (hb : d268205 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36312, d268205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36312, d268205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68641 (p : Pattern) (ha : d268225 p = 1) (hb : d270878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36307 q = 1) (hb : d268104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d268104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68283 q ha hb
    | true =>
      simp only [d36307, d268104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68284 q ha hb
  have h3 (q : Pattern) (ha : d36308 q = 1) (hb : d268198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d268198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36308, d268198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268201 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36309 q = 1) (hb : d268202 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d268202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36309, d268202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36310 q = 1) (hb : d268223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d268223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d268223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36311 q = 1) (hb : d268224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d268224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d268224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268225 q = 1) (hb : d270878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268225, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268225, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68642 (p : Pattern) (ha : d268293 p = 1) (hb : d270889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268282 q = 1) (hb : d270884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268282, d270884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68319 q hb ha
    | true =>
      simp only [d268282, d270884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68290 q hb ha
  have h3 (q : Pattern) (ha : d268283 q = 1) (hb : d270885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268283, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268283, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268289 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268290 q = 1) (hb : d270886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268290, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268290, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268291 q = 1) (hb : d270887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268291, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268291, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268292 q = 1) (hb : d270888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268292, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268292, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268293 q = 1) (hb : d270889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268293, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268293, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68643 (p : Pattern) (ha : d268306 p = 1) (hb : d270895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36313 q = 1) (hb : d268206 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d268206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68639 q ha hb
    | true =>
      simp only [d36313, d268206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68640 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36314 q = 1) (hb : d268220 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d268220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36314, d268220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268221 q = 1) (hb : d270876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268221, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268221, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268222 q = 1) (hb : d270877 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268222, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268222, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268226 q = 1) (hb : d270879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268226, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268226, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68641 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268228 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268229 q = 1) (hb : d270880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268229, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268229, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268230 q = 1) (hb : d270881 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268230, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268230, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268231 q = 1) (hb : d270882 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268231, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268231, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268232 q = 1) (hb : d270883 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268232, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268232, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268294 q = 1) (hb : d270890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268294, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268294, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68642 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268301 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268302 q = 1) (hb : d270891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268302, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268302, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268303 q = 1) (hb : d270892 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268303, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268303, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268304 q = 1) (hb : d270893 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268304, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268304, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268305 q = 1) (hb : d270894 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268305, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268305, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268306 q = 1) (hb : d270895 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268306, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268306, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68644 (p : Pattern) (ha : d268312 p = 1) (hb : d270901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268307 q = 1) (hb : d270896 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268307, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268307, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68643 q ha hb
  have h2 (q : Pattern) (ha : d268308 q = 1) (hb : d270897 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268308, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268308, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268309 q = 1) (hb : d270898 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268309, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268309, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268310 q = 1) (hb : d270899 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268310, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268310, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268311 q = 1) (hb : d270900 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268311, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268311, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268312 q = 1) (hb : d270901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268312, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268312, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68645 (p : Pattern) (ha : d36634 p = 1) (hb : d268439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268428 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36629 q = 1) (hb : d268349 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d268349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68330 q ha hb
    | true =>
      simp only [d36629, d268349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68331 q ha hb
  have h5 (q : Pattern) (ha : d36630 q = 1) (hb : d268429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d268429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36630, d268429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36631 q = 1) (hb : d268436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d268436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36631, d268436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36632 q = 1) (hb : d268437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d268437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36632, d268437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36633 q = 1) (hb : d268438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d268438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36633, d268438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36634 q = 1) (hb : d268439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36634, d268439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36634, d268439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68646 (p : Pattern) (ha : d36644 p = 1) (hb : d268460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268375 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268428 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36629 q = 1) (hb : d268349 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d268349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68330 q ha hb
    | true =>
      simp only [d36629, d268349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68331 q ha hb
  have h4 (q : Pattern) (ha : d36630 q = 1) (hb : d268429 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d268429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36630, d268429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36631 q = 1) (hb : d268436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d268436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36631, d268436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36632 q = 1) (hb : d268437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d268437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36632, d268437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36633 q = 1) (hb : d268438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d268438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d268438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268452 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36639 q = 1) (hb : d268359 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d268359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68333 q ha hb
    | true =>
      simp only [d36639, d268359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68334 q ha hb
  have h13 (q : Pattern) (ha : d36640 q = 1) (hb : d268453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d268453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36640, d268453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36641 q = 1) (hb : d268457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d268457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36641, d268457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36642 q = 1) (hb : d268458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d268458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36642, d268458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36643 q = 1) (hb : d268459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d268459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36643, d268459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36644 q = 1) (hb : d268460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36644, d268460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36644, d268460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68647 (p : Pattern) (ha : d268480 p = 1) (hb : d270905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36639 q = 1) (hb : d268359 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d268359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68333 q ha hb
    | true =>
      simp only [d36639, d268359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68334 q ha hb
  have h3 (q : Pattern) (ha : d36640 q = 1) (hb : d268453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d268453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36640, d268453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268456 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36641 q = 1) (hb : d268457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d268457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36641, d268457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36642 q = 1) (hb : d268478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d268478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d268478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36643 q = 1) (hb : d268479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d268479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d268479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268480 q = 1) (hb : d270905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268480, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268480, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68648 (p : Pattern) (ha : d268565 p = 1) (hb : d270916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268554 q = 1) (hb : d270911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268554, d270911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68372 q hb ha
    | true =>
      simp only [d268554, d270911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68342 q hb ha
  have h3 (q : Pattern) (ha : d268555 q = 1) (hb : d270912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268555, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268555, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268561 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268562 q = 1) (hb : d270913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268562, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268562, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268563 q = 1) (hb : d270914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268563, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268563, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268564 q = 1) (hb : d270915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268564, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268564, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268565 q = 1) (hb : d270916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268565, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268565, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68649 (p : Pattern) (ha : d268578 p = 1) (hb : d270922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36645 q = 1) (hb : d268461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36645, d268461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68645 q ha hb
    | true =>
      simp only [d36645, d268461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68646 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36646 q = 1) (hb : d268475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36646, d268475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36646, d268475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268476 q = 1) (hb : d270903 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268476, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268476, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268477 q = 1) (hb : d270904 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268477, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268477, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268481 q = 1) (hb : d270906 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268481, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268481, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68647 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268483 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268484 q = 1) (hb : d270907 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268484, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268484, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268485 q = 1) (hb : d270908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268485, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268485, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268486 q = 1) (hb : d270909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268486, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268486, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268487 q = 1) (hb : d270910 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268487, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268487, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268566 q = 1) (hb : d270917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268566, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268566, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68648 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268573 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268574 q = 1) (hb : d270918 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268574, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268574, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268575 q = 1) (hb : d270919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268575, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268575, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268576 q = 1) (hb : d270920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268576, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268576, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268577 q = 1) (hb : d270921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268577, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268577, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268578 q = 1) (hb : d270922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268578, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268578, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68650 (p : Pattern) (ha : d268584 p = 1) (hb : d270928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268579 q = 1) (hb : d270923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268579, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268579, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68649 q ha hb
  have h2 (q : Pattern) (ha : d268580 q = 1) (hb : d270924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268580, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268580, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268581 q = 1) (hb : d270925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268581, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268581, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268582 q = 1) (hb : d270926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268582, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268582, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268583 q = 1) (hb : d270927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268583, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268583, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268584 q = 1) (hb : d270928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268584, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268584, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68651 (p : Pattern) (ha : d37065 p = 1) (hb : d268774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d268754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d37060 q = 1) (hb : d268669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37060, d268669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68388 q ha hb
    | true =>
      simp only [d37060, d268669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68389 q ha hb
  have h5 (q : Pattern) (ha : d37061 q = 1) (hb : d268755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d268755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37061, d268755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d268770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d37062 q = 1) (hb : d268771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d268771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d37062, d268771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37063 q = 1) (hb : d268772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d268772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37063, d268772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d37064 q = 1) (hb : d268773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d268773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37064, d268773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d37065 q = 1) (hb : d268774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37065, d268774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37065, d268774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68652 (p : Pattern) (ha : d37075 p = 1) (hb : d268795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268695 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37060 q = 1) (hb : d268669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37060, d268669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68388 q ha hb
    | true =>
      simp only [d37060, d268669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68389 q ha hb
  have h4 (q : Pattern) (ha : d37061 q = 1) (hb : d268755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d268755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37061, d268755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d268770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d37062 q = 1) (hb : d268771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d268771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d37062, d268771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37063 q = 1) (hb : d268772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d268772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37063, d268772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37064 q = 1) (hb : d268773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d268773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37064, d268773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d268780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d268785 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d268787 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d37070 q = 1) (hb : d268679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d268679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68391 q ha hb
    | true =>
      simp only [d37070, d268679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68392 q ha hb
  have h13 (q : Pattern) (ha : d37071 q = 1) (hb : d268788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d268788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d37071, d268788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268791 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d37072 q = 1) (hb : d268792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d268792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d37072, d268792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d37073 q = 1) (hb : d268793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d268793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37073, d268793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d37074 q = 1) (hb : d268794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d268794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d37074, d268794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d37075 q = 1) (hb : d268795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37075, d268795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d37075, d268795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68653 (p : Pattern) (ha : d268815 p = 1) (hb : d270933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37070 q = 1) (hb : d268679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d268679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68391 q ha hb
    | true =>
      simp only [d37070, d268679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68392 q ha hb
  have h3 (q : Pattern) (ha : d37071 q = 1) (hb : d268788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d268788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37071, d268788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268791 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37072 q = 1) (hb : d268792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d268792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37072, d268792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37073 q = 1) (hb : d268813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d268813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d268813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37074 q = 1) (hb : d268814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d268814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d268814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268815 q = 1) (hb : d270933 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268815, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268815, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68654 (p : Pattern) (ha : d268936 p = 1) (hb : d270944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d268911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268916 q = 1) (hb : d270939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d268916, d270939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68432 q hb ha
    | true =>
      simp only [d268916, d270939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68400 q hb ha
  have h3 (q : Pattern) (ha : d268917 q = 1) (hb : d270940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d268917, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268917, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d268932 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268933 q = 1) (hb : d270941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d268933, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268933, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268934 q = 1) (hb : d270942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d268934, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268934, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268935 q = 1) (hb : d270943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d268935, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268935, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d268936 q = 1) (hb : d270944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d268936, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268936, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68655 (p : Pattern) (ha : d268949 p = 1) (hb : d270950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d268687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d268796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d268796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68651 q ha hb
    | true =>
      simp only [d37076, d268796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68652 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d268809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37077 q = 1) (hb : d268810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d268810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d268810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d268811 q = 1) (hb : d270931 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268811, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d268811, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d268812 q = 1) (hb : d270932 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268812, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268812, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d268816 q = 1) (hb : d270934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268816, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268816, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68653 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d268818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d268819 q = 1) (hb : d270935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268819, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d268819, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d268820 q = 1) (hb : d270936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268820, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d268820, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d268821 q = 1) (hb : d270937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268821, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d268821, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d268822 q = 1) (hb : d270938 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268822, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d268822, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d268937 q = 1) (hb : d270945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d268937, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d268937, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68654 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d268944 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d268945 q = 1) (hb : d270946 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d268945, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d268945, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d268946 q = 1) (hb : d270947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d268946, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d268946, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d268947 q = 1) (hb : d270948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d268947, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d268947, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d268948 q = 1) (hb : d270949 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d268948, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d268948, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d268949 q = 1) (hb : d270950 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d268949, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d268949, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68656 (p : Pattern) (ha : d268955 p = 1) (hb : d270956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d268950 q = 1) (hb : d270951 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d268950, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268950, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68655 q ha hb
  have h2 (q : Pattern) (ha : d268951 q = 1) (hb : d270952 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d268951, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268951, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d268952 q = 1) (hb : d270953 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d268952, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268952, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268953 q = 1) (hb : d270954 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d268953, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268953, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d268954 q = 1) (hb : d270955 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d268954, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268954, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268955 q = 1) (hb : d270956 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d268955, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d268955, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68657 (p : Pattern) (ha : d269204 p = 1) (hb : d270198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d269171 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269086 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269086, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68456 q ha hb
    | true =>
      simp only [d269086, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68457 q ha hb
  have h5 (q : Pattern) (ha : d269172 q = 1) (hb : d270194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269172, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d269200 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269201 q = 1) (hb : d270195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269201, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269202 q = 1) (hb : d270196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269202, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269203 q = 1) (hb : d270197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269203, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269204 q = 1) (hb : d270198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269204, d270198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269204, d270198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68658 (p : Pattern) (ha : d269226 p = 1) (hb : d270208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269086 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269086, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68456 q ha hb
    | true =>
      simp only [d269086, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68457 q ha hb
  have h4 (q : Pattern) (ha : d269172 q = 1) (hb : d270194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269172, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269172, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269200 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269201 q = 1) (hb : d270195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269201, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269201, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269202 q = 1) (hb : d270196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269202, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269202, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269203 q = 1) (hb : d270197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269203, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269203, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269210 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269215 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d269218 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d269096 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269096, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68459 q ha hb
    | true =>
      simp only [d269096, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68460 q ha hb
  have h13 (q : Pattern) (ha : d269219 q = 1) (hb : d270204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269219, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269222 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269223 q = 1) (hb : d270205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269223, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269224 q = 1) (hb : d270206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269224, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269224, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269225 q = 1) (hb : d270207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269225, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269225, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269226 q = 1) (hb : d270208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269226, d270208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269226, d270208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68659 (p : Pattern) (ha : d269251 p = 1) (hb : d270962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269096 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269096, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68459 q ha hb
    | true =>
      simp only [d269096, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68460 q ha hb
  have h3 (q : Pattern) (ha : d269219 q = 1) (hb : d270204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269219, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269219, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269222 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269223 q = 1) (hb : d270205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269223, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269223, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269249 q = 1) (hb : d270206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269249, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269249, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269250 q = 1) (hb : d270207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269250, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269250, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269251 q = 1) (hb : d270962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269251, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269251, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68660 (p : Pattern) (ha : d269360 p = 1) (hb : d270969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269313 q = 1) (hb : d270378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269313, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68495 q ha hb
    | true =>
      simp only [d269313, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
  have h2 (q : Pattern) (ha : d269314 q = 1) (hb : d270379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269314, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269314, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269315 q = 1) (hb : d270380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269315, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269315, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269327 q = 1) (hb : d270392 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269327, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
    | true =>
      simp only [d269327, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68498 q ha hb
  have h5 (q : Pattern) (ha : d269328 q = 1) (hb : d270393 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269328, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269328, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269329 q = 1) (hb : d270394 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269329, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269329, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269330 q = 1) (hb : d270395 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269330, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269330, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269346 q = 1) (hb : d270411 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269346, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68497 q ha hb
    | true =>
      simp only [d269346, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68502 q ha hb
  have h9 (q : Pattern) (ha : d269347 q = 1) (hb : d270412 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269347, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269347, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269348 q = 1) (hb : d270413 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269348, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269348, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269349 q = 1) (hb : d270414 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269349, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269349, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269359 q = 1) (hb : d270968 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269359, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269359, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269360 q = 1) (hb : d270969 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269360, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269360, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro68661 (p : Pattern) (ha : d269366 p = 1) (hb : d270975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269361 q = 1) (hb : d270970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269361, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68660 q ha hb
    | true =>
      simp only [d269361, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269362 q = 1) (hb : d270971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269362, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269362, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269352 q = 1) (hb : d270417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269352, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68503 q ha hb
    | true =>
      simp only [d269352, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269353 q = 1) (hb : d270418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269353, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269353, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269363 q = 1) (hb : d270972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269363, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269363, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269364 q = 1) (hb : d270973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269364, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269364, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269365 q = 1) (hb : d270974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269365, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269365, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269366 q = 1) (hb : d270975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269366, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269366, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68662 (p : Pattern) (ha : d269402 p = 1) (hb : d270981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269371 q = 1) (hb : d270976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269371, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68661 q ha hb
    | true =>
      simp only [d269371, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68510 q ha hb
  have h3 (q : Pattern) (ha : d269372 q = 1) (hb : d270977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269372, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269372, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269399 q = 1) (hb : d270978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269399, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269399, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269400 q = 1) (hb : d270979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269400, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269400, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269401 q = 1) (hb : d270980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269401, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269401, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269402 q = 1) (hb : d270981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269402, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269402, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68663 (p : Pattern) (ha : d269415 p = 1) (hb : d270987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269227 q = 1) (hb : d270209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269227, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68657 q ha hb
    | true =>
      simp only [d269227, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68658 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269246 q = 1) (hb : d270210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269246, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269246, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269247 q = 1) (hb : d270960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269247, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269247, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269248 q = 1) (hb : d270961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269248, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269248, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269252 q = 1) (hb : d270963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269252, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269252, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68659 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269254 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269255 q = 1) (hb : d270964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269255, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269255, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269256 q = 1) (hb : d270965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269256, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269256, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d269257 q = 1) (hb : d270966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269257, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269257, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269258 q = 1) (hb : d270967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269258, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269258, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269403 q = 1) (hb : d270982 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269403, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269403, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68662 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269411 q = 1) (hb : d270983 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269411, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269411, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269412 q = 1) (hb : d270984 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269412, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269412, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d269413 q = 1) (hb : d270985 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269413, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269413, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d269414 q = 1) (hb : d270986 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269414, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269414, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d269415 q = 1) (hb : d270987 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269415, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269415, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68664 (p : Pattern) (ha : d269421 p = 1) (hb : d270993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269416 q = 1) (hb : d270988 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269416, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269416, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68663 q ha hb
  have h2 (q : Pattern) (ha : d269417 q = 1) (hb : d270989 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269417, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269417, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269418 q = 1) (hb : d270990 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269418, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269418, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269419 q = 1) (hb : d270991 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269419, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269419, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269420 q = 1) (hb : d270992 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269420, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269420, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269421 q = 1) (hb : d270993 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269421, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269421, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68665 (p : Pattern) (ha : d269633 p = 1) (hb : d270553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d269537 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68529 q ha hb
    | true =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
  have h5 (q : Pattern) (ha : d269601 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269601, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269630 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269630, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d269631 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269631, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269632 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269632, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269633 q = 1) (hb : d270553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269633, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269633, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68666 (p : Pattern) (ha : d269655 p = 1) (hb : d270563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269537 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68529 q ha hb
    | true =>
      simp only [d269537, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68530 q ha hb
  have h4 (q : Pattern) (ha : d269601 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269601, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d269601, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d269629 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d269630 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269630, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269630, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d269631 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269631, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269631, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269632 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269632, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269632, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d269639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d269644 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d269547 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269547, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68532 q ha hb
    | true =>
      simp only [d269547, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68533 q ha hb
  have h13 (q : Pattern) (ha : d269648 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d269648, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269652 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269652, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269653 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269653, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269653, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269654 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269654, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d269654, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269655 q = 1) (hb : d270563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269655, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269655, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68667 (p : Pattern) (ha : d269680 p = 1) (hb : d271000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269547 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269547, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68532 q ha hb
    | true =>
      simp only [d269547, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68533 q ha hb
  have h3 (q : Pattern) (ha : d269648 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269648, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269648, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269652 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269652, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269652, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269678 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269678, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269678, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269679 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269679, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269679, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269680 q = 1) (hb : d271000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269680, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269680, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68668 (p : Pattern) (ha : d269775 p = 1) (hb : d271007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269728 q = 1) (hb : d270714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68563 q ha hb
    | true =>
      simp only [d269728, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
  have h2 (q : Pattern) (ha : d269729 q = 1) (hb : d270715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269729, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269730 q = 1) (hb : d270716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269730, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269742 q = 1) (hb : d270728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269742, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68566 q ha hb
  have h5 (q : Pattern) (ha : d269743 q = 1) (hb : d270729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269743, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269744 q = 1) (hb : d270730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269744, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269745 q = 1) (hb : d270731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269745, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269761 q = 1) (hb : d270747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269761, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269761, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68570 q ha hb
  have h9 (q : Pattern) (ha : d269762 q = 1) (hb : d270748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269762, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269762, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269763 q = 1) (hb : d270749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269763, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269763, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269764 q = 1) (hb : d270750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269764, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269764, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269774 q = 1) (hb : d271006 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269774, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269774, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269775 q = 1) (hb : d271007 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269775, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269775, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro68669 (p : Pattern) (ha : d269781 p = 1) (hb : d271013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269776 q = 1) (hb : d271008 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269776, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68668 q ha hb
    | true =>
      simp only [d269776, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269777 q = 1) (hb : d271009 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269777, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269777, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269767 q = 1) (hb : d270753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269767, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68571 q ha hb
    | true =>
      simp only [d269767, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269768 q = 1) (hb : d270754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269768, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269768, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269778 q = 1) (hb : d271010 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269778, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269778, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269779 q = 1) (hb : d271011 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269779, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269779, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269780 q = 1) (hb : d271012 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269780, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269780, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269781 q = 1) (hb : d271013 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269781, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269781, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro68670 (p : Pattern) (ha : d269789 p = 1) (hb : d270515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d269785 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d269785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5239, d269785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27181 q = 1) (hb : d269786 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, d269786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27181, d269786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d269459 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2048, d269459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2061 q = 1) (hb : d269460 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2061, d269460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27182 q = 1) (hb : d269787 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27182, d269787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27182, d269787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27183 q = 1) (hb : d269788 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27183, d269788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27183, d269788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d269789 q = 1) (hb : d270515 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d269789, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d269789, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro68671 (p : Pattern) (ha : d269795 p = 1) (hb : d270746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269722 q = 1) (hb : d270708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269722, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
  have h2 (q : Pattern) (ha : d269482 q = 1) (hb : d270496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68521 q ha hb
    | true =>
      simp only [d269482, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269723 q = 1) (hb : d270709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269723, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269483 q = 1) (hb : d270497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269483, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269724 q = 1) (hb : d270710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269724, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269725 q = 1) (hb : d270711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269725, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d269759 q = 1) (hb : d270745 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269759, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269759, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d269736 q = 1) (hb : d270722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269736, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269736, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
  have h9 (q : Pattern) (ha : d269505 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68524 q ha hb
    | true =>
      simp only [d269505, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d269737 q = 1) (hb : d270723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269737, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269737, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269790 q = 1) (hb : d270516 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d269790, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68670 q ha hb
    | true =>
      simp only [d269790, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d269791 q = 1) (hb : d270517 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d269791, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269791, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d269792 q = 1) (hb : d270724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d269792, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269792, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269793 q = 1) (hb : d270725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d269793, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269793, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d269794 q = 1) (hb : d270726 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d269794, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269794, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d269795 q = 1) (hb : d270746 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d269795, d270746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269795, d270746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro68672 (p : Pattern) (ha : d269801 p = 1) (hb : d270752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269796 q = 1) (hb : d270747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d269796, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68565 q ha hb
    | true =>
      simp only [d269796, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68671 q ha hb
  have h2 (q : Pattern) (ha : d269797 q = 1) (hb : d270748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d269797, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269797, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269798 q = 1) (hb : d270749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d269798, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269798, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269799 q = 1) (hb : d270750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d269799, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269799, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269800 q = 1) (hb : d270751 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d269800, d270751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269800, d270751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269801 q = 1) (hb : d270752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d269801, d270752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269801, d270752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68673 (p : Pattern) (ha : d269807 p = 1) (hb : d270784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269802 q = 1) (hb : d270753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d269802, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68672 q ha hb
    | true =>
      simp only [d269802, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269803 q = 1) (hb : d270754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d269803, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269803, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269804 q = 1) (hb : d270781 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d269804, d270781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269804, d270781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269805 q = 1) (hb : d270782 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d269805, d270782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269805, d270782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269806 q = 1) (hb : d270783 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d269806, d270783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269806, d270783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269807 q = 1) (hb : d270784 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d269807, d270784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269807, d270784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68674 (p : Pattern) (ha : d269839 p = 1) (hb : d271019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d269773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269808 q = 1) (hb : d271014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d269808, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68669 q ha hb
    | true =>
      simp only [d269808, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68673 q ha hb
  have h3 (q : Pattern) (ha : d269809 q = 1) (hb : d271015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269809, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269809, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d269835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269836 q = 1) (hb : d271016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269836, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269836, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269837 q = 1) (hb : d271017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269837, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269837, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269838 q = 1) (hb : d271018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269838, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269838, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269839 q = 1) (hb : d271019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269839, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269839, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68675 (p : Pattern) (ha : d269856 p = 1) (hb : d271025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d269555 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269656 q = 1) (hb : d270564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269656, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68665 q ha hb
    | true =>
      simp only [d269656, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68666 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d269674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269675 q = 1) (hb : d270565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269675, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269675, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269676 q = 1) (hb : d270998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269676, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269676, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269677 q = 1) (hb : d270999 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269677, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269677, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269681 q = 1) (hb : d271001 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269681, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269681, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68667 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d269683 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269684 q = 1) (hb : d271002 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269684, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269684, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269685 q = 1) (hb : d271003 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269685, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269685, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d269686 q = 1) (hb : d271004 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269686, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269686, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d269687 q = 1) (hb : d271005 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269687, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269687, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269840 q = 1) (hb : d271020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269840, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269840, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68674 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d269851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269852 q = 1) (hb : d271021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269852, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269852, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269853 q = 1) (hb : d271022 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269853, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269853, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d269854 q = 1) (hb : d271023 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269854, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269854, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d269855 q = 1) (hb : d271024 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269855, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269855, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d269856 q = 1) (hb : d271025 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269856, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269856, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68676 (p : Pattern) (ha : d269862 p = 1) (hb : d271031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269857 q = 1) (hb : d271026 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269857, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269857, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68675 q ha hb
  have h2 (q : Pattern) (ha : d269858 q = 1) (hb : d271027 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269858, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269858, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269859 q = 1) (hb : d271028 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269859, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269859, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269860 q = 1) (hb : d271029 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269860, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269860, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269861 q = 1) (hb : d271030 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269861, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269861, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269862 q = 1) (hb : d271031 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269862, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269862, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68677 (p : Pattern) (ha : d269868 p = 1) (hb : d271037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d268313 q = 1) (hb : d270902 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268313, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68638 q ha hb
    | true =>
      simp only [d268313, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68644 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d268585 q = 1) (hb : d270929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268585, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268585, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68650 q ha hb
  have h3 (q : Pattern) (ha : d268586 q = 1) (hb : d270930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268586, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d268586, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d268956 q = 1) (hb : d270957 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d268956, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268956, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68656 q ha hb
  have h5 (q : Pattern) (ha : d268957 q = 1) (hb : d270958 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d268957, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d268957, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d268958 q = 1) (hb : d270959 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d268958, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d268958, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269422 q = 1) (hb : d270994 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269422, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269422, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68664 q ha hb
  have h8 (q : Pattern) (ha : d269423 q = 1) (hb : d270995 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269423, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269423, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269424 q = 1) (hb : d270996 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269424, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269424, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269425 q = 1) (hb : d270997 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269425, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269425, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269863 q = 1) (hb : d271032 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d269863, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269863, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68676 q ha hb
  have h12 (q : Pattern) (ha : d269864 q = 1) (hb : d271033 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d269864, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269864, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269865 q = 1) (hb : d271034 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d269865, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269865, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269866 q = 1) (hb : d271035 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d269866, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269866, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269867 q = 1) (hb : d271036 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d269867, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269867, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269868 q = 1) (hb : d271037 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d269868, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269868, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro68678 (p : Pattern) (ha : d269874 p = 1) (hb : d271043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269869 q = 1) (hb : d271038 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d269869, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68677 q ha hb
    | true =>
      simp only [d269869, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269870 q = 1) (hb : d271039 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d269870, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269870, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269871 q = 1) (hb : d271040 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d269871, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269871, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269872 q = 1) (hb : d271041 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d269872, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269872, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269873 q = 1) (hb : d271042 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d269873, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269873, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269874 q = 1) (hb : d271043 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d269874, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269874, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68679 (p : Pattern) (ha : d269880 p = 1) (hb : d271049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269875 q = 1) (hb : d271044 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d269875, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68678 q ha hb
    | true =>
      simp only [d269875, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269876 q = 1) (hb : d271045 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d269876, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269876, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269877 q = 1) (hb : d271046 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d269877, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269877, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269878 q = 1) (hb : d271047 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d269878, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269878, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269879 q = 1) (hb : d271048 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d269879, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269879, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269880 q = 1) (hb : d271049 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d269880, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269880, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68680 (p : Pattern) (ha : d269886 p = 1) (hb : d271055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269881 q = 1) (hb : d271050 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d269881, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68679 q ha hb
    | true =>
      simp only [d269881, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269882 q = 1) (hb : d271051 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d269882, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269882, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269883 q = 1) (hb : d271052 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d269883, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269883, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269884 q = 1) (hb : d271053 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d269884, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269884, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269885 q = 1) (hb : d271054 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d269885, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269885, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269886 q = 1) (hb : d271055 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d269886, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269886, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68681 (p : Pattern) (ha : d269892 p = 1) (hb : d271061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269887 q = 1) (hb : d271056 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d269887, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68680 q ha hb
    | true =>
      simp only [d269887, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269888 q = 1) (hb : d271057 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d269888, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269888, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269889 q = 1) (hb : d271058 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d269889, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269889, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269890 q = 1) (hb : d271059 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d269890, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269890, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269891 q = 1) (hb : d271060 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d269891, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269891, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269892 q = 1) (hb : d271061 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d269892, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269892, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68682 (p : Pattern) (ha : d269898 p = 1) (hb : d271067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269893 q = 1) (hb : d271062 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d269893, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68681 q ha hb
    | true =>
      simp only [d269893, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269894 q = 1) (hb : d271063 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d269894, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269894, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269895 q = 1) (hb : d271064 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d269895, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269895, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269896 q = 1) (hb : d271065 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d269896, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269896, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269897 q = 1) (hb : d271066 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d269897, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269897, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269898 q = 1) (hb : d271067 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d269898, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269898, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68683 (p : Pattern) (ha : d269904 p = 1) (hb : d271073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269899 q = 1) (hb : d271068 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d269899, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68682 q ha hb
    | true =>
      simp only [d269899, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269900 q = 1) (hb : d271069 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d269900, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269900, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269901 q = 1) (hb : d271070 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d269901, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269901, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269902 q = 1) (hb : d271071 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d269902, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269902, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269903 q = 1) (hb : d271072 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d269903, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269903, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269904 q = 1) (hb : d271073 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d269904, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269904, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68684 (p : Pattern) (ha : d269910 p = 1) (hb : d271079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269905 q = 1) (hb : d271074 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d269905, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68683 q ha hb
    | true =>
      simp only [d269905, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d269906 q = 1) (hb : d271075 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d269906, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269906, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d269907 q = 1) (hb : d271076 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d269907, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269907, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d269908 q = 1) (hb : d271077 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d269908, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269908, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d269909 q = 1) (hb : d271078 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d269909, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269909, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d269910 q = 1) (hb : d271079 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d269910, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269910, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro68685 (p : Pattern) (ha : d104 p = 1) (hb : d269915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d269911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d269912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d269913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d269914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d269915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d269915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d269915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68686 (p : Pattern) (ha : d111 p = 1) (hb : d269920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36026 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d269911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d269912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d269913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d269914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36033 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d269916 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d269917 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d269918 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d269918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d269918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d269919 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d269919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d269919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d269920 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d269920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d269920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68687 (p : Pattern) (ha : d406 p = 1) (hb : d269927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d269916 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d269917 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d269925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d269925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d269925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d269926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d269926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d269926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d269927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d269927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d269927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68688 (p : Pattern) (ha : d462 p = 1) (hb : d269937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d269933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d269933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d269933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d269934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d269934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d269934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d269935 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d269935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d269935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d269936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d269936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d269936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d269937 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d269937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d269937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68689 (p : Pattern) (ha : d53647 p = 1) (hb : d269943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d269921 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d269921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68685 q ha hb
    | true =>
      simp only [d112, d269921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68686 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d269922 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d269922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d269922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d269923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d269923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d269923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d269924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d269924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d269924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d269928 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d269928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d269928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68687 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d269929 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d269929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d269929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d269930 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d269930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d269930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d269931 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d269931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d269931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d269932 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d269932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d269932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d269938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d269938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d269938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68688 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d269939 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d269939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d269939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d269940 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d269940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d269940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d269941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d269941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d269941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d269942 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d269942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d269942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d269943 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d269943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d269943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro68690 (p : Pattern) (ha : d36090 p = 1) (hb : d269953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36112 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36086 q = 1) (hb : d269949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36086, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36174 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36087 q = 1) (hb : d269950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36087, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36088 q = 1) (hb : d269951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36088, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36089 q = 1) (hb : d269952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36089, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36090 q = 1) (hb : d269953 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36090, d269953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36090, d269953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68691 (p : Pattern) (ha : d36097 p = 1) (hb : d269958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36086 q = 1) (hb : d269949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36086, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36174 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36087 q = 1) (hb : d269950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36087, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36088 q = 1) (hb : d269951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36088, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36089 q = 1) (hb : d269952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36187 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36189 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d36033 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36093 q = 1) (hb : d269954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36093, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36195 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36094 q = 1) (hb : d269955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36094, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36095 q = 1) (hb : d269956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d269956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36095, d269956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36096 q = 1) (hb : d269957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d269957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36096, d269957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36097 q = 1) (hb : d269958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36097, d269958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36097, d269958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68692 (p : Pattern) (ha : d269965 p = 1) (hb : d270853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36093 q = 1) (hb : d269954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36093, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36094 q = 1) (hb : d269955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36094, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36095 q = 1) (hb : d269963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d269963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d269963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36096 q = 1) (hb : d269964 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d269964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d269964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269965 q = 1) (hb : d270853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269965, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269965, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68693 (p : Pattern) (ha : d269975 p = 1) (hb : d270863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36237 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36069 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269971 q = 1) (hb : d270859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269971, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269971, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269972 q = 1) (hb : d270860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269972, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269972, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d269973 q = 1) (hb : d270861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269973, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269973, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269974 q = 1) (hb : d270862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269974, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269974, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269975 q = 1) (hb : d270863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269975, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269975, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68694 (p : Pattern) (ha : d269981 p = 1) (hb : d270869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36098 q = 1) (hb : d269959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d269959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68690 q ha hb
    | true =>
      simp only [d36098, d269959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68691 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36099 q = 1) (hb : d269960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d269960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36099, d269960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269961 q = 1) (hb : d270851 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269961, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d269961, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269962 q = 1) (hb : d270852 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269962, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269962, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269966 q = 1) (hb : d270854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269966, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269966, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68692 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d269967 q = 1) (hb : d270855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269967, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269967, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d269968 q = 1) (hb : d270856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269968, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269968, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d269969 q = 1) (hb : d270857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269969, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269969, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d269970 q = 1) (hb : d270858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269970, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269970, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269976 q = 1) (hb : d270864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269976, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269976, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68693 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d269977 q = 1) (hb : d270865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269977, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269977, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d269978 q = 1) (hb : d270866 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269978, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269978, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d269979 q = 1) (hb : d270867 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269979, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269979, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d269980 q = 1) (hb : d270868 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269980, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269980, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d269981 q = 1) (hb : d270869 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269981, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269981, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68695 (p : Pattern) (ha : d269987 p = 1) (hb : d270875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d269944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68689 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d269945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d269946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d269947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d269948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269982 q = 1) (hb : d270870 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269982, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269982, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68694 q ha hb
  have h8 (q : Pattern) (ha : d269983 q = 1) (hb : d270871 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269983, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269983, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269984 q = 1) (hb : d270872 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269984, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269984, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269985 q = 1) (hb : d270873 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269985, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269985, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269986 q = 1) (hb : d270874 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269986, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269986, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269987 q = 1) (hb : d270875 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269987, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d269987, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro68696 (p : Pattern) (ha : d36302 p = 1) (hb : d269992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36323 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36332 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36297 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36298 q = 1) (hb : d269988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36298, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36425 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36299 q = 1) (hb : d269989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36299, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36300 q = 1) (hb : d269990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36300, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36301 q = 1) (hb : d269991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36301, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36302 q = 1) (hb : d269992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36302, d269992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36302, d269992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68697 (p : Pattern) (ha : d36312 p = 1) (hb : d269997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36298 q = 1) (hb : d269988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36298, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36425 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36299 q = 1) (hb : d269989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36299, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36300 q = 1) (hb : d269990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36300, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36301 q = 1) (hb : d269991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36440 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36442 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d36307 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36308 q = 1) (hb : d269993 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36308, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36449 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36309 q = 1) (hb : d269994 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36309, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36310 q = 1) (hb : d269995 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d269995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36310, d269995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36311 q = 1) (hb : d269996 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d269996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36311, d269996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36312 q = 1) (hb : d269997 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36312, d269997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36312, d269997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68698 (p : Pattern) (ha : d270004 p = 1) (hb : d270878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36307 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36308 q = 1) (hb : d269993 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36308, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36449 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36309 q = 1) (hb : d269994 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36309, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36310 q = 1) (hb : d270002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d270002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d270002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36311 q = 1) (hb : d270003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d270003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d270003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270004 q = 1) (hb : d270878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270004, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270004, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68699 (p : Pattern) (ha : d270014 p = 1) (hb : d270889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270010 q = 1) (hb : d270885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270010, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270010, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270011 q = 1) (hb : d270886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270011, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270011, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270012 q = 1) (hb : d270887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270012, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270012, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270013 q = 1) (hb : d270888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270013, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270013, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270014 q = 1) (hb : d270889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270014, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270014, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68700 (p : Pattern) (ha : d270020 p = 1) (hb : d270895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36313 q = 1) (hb : d269998 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d269998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68696 q ha hb
    | true =>
      simp only [d36313, d269998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68697 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36314 q = 1) (hb : d269999 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d269999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36314, d269999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270000 q = 1) (hb : d270876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270000, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270000, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270001 q = 1) (hb : d270877 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270001, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270001, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270005 q = 1) (hb : d270879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270005, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270005, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68698 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d36476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270006 q = 1) (hb : d270880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270006, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270006, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270007 q = 1) (hb : d270881 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270007, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270007, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270008 q = 1) (hb : d270882 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270008, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270008, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270009 q = 1) (hb : d270883 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270009, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270009, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270015 q = 1) (hb : d270890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270015, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270015, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68699 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36581 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270016 q = 1) (hb : d270891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270016, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270016, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270017 q = 1) (hb : d270892 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270017, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270017, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270018 q = 1) (hb : d270893 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270018, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270018, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270019 q = 1) (hb : d270894 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270019, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270019, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270020 q = 1) (hb : d270895 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270020, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270020, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68701 (p : Pattern) (ha : d270026 p = 1) (hb : d270901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270021 q = 1) (hb : d270896 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270021, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270021, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68700 q ha hb
  have h2 (q : Pattern) (ha : d270022 q = 1) (hb : d270897 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270022, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270022, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270023 q = 1) (hb : d270898 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270023, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270023, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270024 q = 1) (hb : d270899 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270024, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270024, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270025 q = 1) (hb : d270900 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270025, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270025, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270026 q = 1) (hb : d270901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270026, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270026, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68702 (p : Pattern) (ha : d36634 p = 1) (hb : d270032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36655 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36708 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36629 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36630 q = 1) (hb : d270028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36630, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36776 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36631 q = 1) (hb : d270029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36631, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36632 q = 1) (hb : d270030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36632, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36633 q = 1) (hb : d270031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36633, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36634 q = 1) (hb : d270032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36634, d270032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36634, d270032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68703 (p : Pattern) (ha : d36644 p = 1) (hb : d270037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36655 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36629 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36630 q = 1) (hb : d270028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36630, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d36776 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36631 q = 1) (hb : d270029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36631, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36632 q = 1) (hb : d270030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36632, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36633 q = 1) (hb : d270031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d36786 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d36791 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d36793 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d36639 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36640 q = 1) (hb : d270033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36640, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36800 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36641 q = 1) (hb : d270034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36641, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36642 q = 1) (hb : d270035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d270035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36642, d270035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36643 q = 1) (hb : d270036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d270036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36643, d270036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36644 q = 1) (hb : d270037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36644, d270037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36644, d270037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68704 (p : Pattern) (ha : d270044 p = 1) (hb : d270905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36640 q = 1) (hb : d270033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36640, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36800 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36641 q = 1) (hb : d270034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36641, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36642 q = 1) (hb : d270042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d270042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d270042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36643 q = 1) (hb : d270043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d270043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d270043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270044 q = 1) (hb : d270905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270044, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270044, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68705 (p : Pattern) (ha : d270054 p = 1) (hb : d270916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d36893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270911 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270050 q = 1) (hb : d270912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270050, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270050, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36948 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270051 q = 1) (hb : d270913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270051, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270051, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270052 q = 1) (hb : d270914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270052, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270052, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270053 q = 1) (hb : d270915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270053, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270053, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270054 q = 1) (hb : d270916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270054, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270054, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68706 (p : Pattern) (ha : d270060 p = 1) (hb : d270922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36647 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36645 q = 1) (hb : d270038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36645, d270038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68702 q ha hb
    | true =>
      simp only [d36645, d270038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68703 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36646 q = 1) (hb : d270039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36646, d270039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36646, d270039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270040 q = 1) (hb : d270903 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270040, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270040, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270041 q = 1) (hb : d270904 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270041, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270041, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270045 q = 1) (hb : d270906 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270045, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270045, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68704 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d36827 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270046 q = 1) (hb : d270907 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270046, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270046, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270047 q = 1) (hb : d270908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270047, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270047, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270048 q = 1) (hb : d270909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270048, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270048, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270049 q = 1) (hb : d270910 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270049, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270049, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270055 q = 1) (hb : d270917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270055, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270055, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68705 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d36964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270056 q = 1) (hb : d270918 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270056, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270056, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270057 q = 1) (hb : d270919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270057, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270057, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270058 q = 1) (hb : d270920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270058, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270058, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270059 q = 1) (hb : d270921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270059, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270059, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270060 q = 1) (hb : d270922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270060, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270060, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68707 (p : Pattern) (ha : d270066 p = 1) (hb : d270928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270061 q = 1) (hb : d270923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270061, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270061, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68706 q ha hb
  have h2 (q : Pattern) (ha : d270062 q = 1) (hb : d270924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270062, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270062, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270063 q = 1) (hb : d270925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270063, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270063, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270064 q = 1) (hb : d270926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270064, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270064, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270065 q = 1) (hb : d270927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270065, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270065, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270066 q = 1) (hb : d270928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270066, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270066, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68708 (p : Pattern) (ha : d37065 p = 1) (hb : d270073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37061 q = 1) (hb : d270069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d270069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37061, d270069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d37247 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d37062 q = 1) (hb : d270070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d270070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d37062, d270070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37063 q = 1) (hb : d270071 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d270071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37063, d270071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d37064 q = 1) (hb : d270072 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d270072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37064, d270072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d37065 q = 1) (hb : d270073 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37065, d270073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37065, d270073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68709 (p : Pattern) (ha : d37075 p = 1) (hb : d270078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37145 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37060 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d37061 q = 1) (hb : d270069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d270069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37061, d270069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37247 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d37062 q = 1) (hb : d270070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d270070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d37062, d270070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37063 q = 1) (hb : d270071 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d270071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37063, d270071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37064 q = 1) (hb : d270072 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d270072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37064, d270072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d37257 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d37262 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d37264 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d37070 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d37071 q = 1) (hb : d270074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d270074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d37071, d270074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37271 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d37072 q = 1) (hb : d270075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d270075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d37072, d270075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d37073 q = 1) (hb : d270076 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d270076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37073, d270076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d37074 q = 1) (hb : d270077 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d270077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d37074, d270077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d37075 q = 1) (hb : d270078 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37075, d270078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d37075, d270078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68710 (p : Pattern) (ha : d270085 p = 1) (hb : d270933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37071 q = 1) (hb : d270074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d270074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37071, d270074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37271 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37072 q = 1) (hb : d270075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d270075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37072, d270075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37073 q = 1) (hb : d270083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d270083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d270083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37074 q = 1) (hb : d270084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d270084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d270084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270085 q = 1) (hb : d270933 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270085, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270085, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro68711 (p : Pattern) (ha : d270095 p = 1) (hb : d270944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270091 q = 1) (hb : d270940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270091, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270091, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270092 q = 1) (hb : d270941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270092, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270092, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d270093 q = 1) (hb : d270942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270093, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270093, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270094 q = 1) (hb : d270943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270094, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270094, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270095 q = 1) (hb : d270944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270095, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270095, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68712 (p : Pattern) (ha : d270101 p = 1) (hb : d270950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d270079 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d270079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68708 q ha hb
    | true =>
      simp only [d37076, d270079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68709 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37077 q = 1) (hb : d270080 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d270080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d270080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270081 q = 1) (hb : d270931 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270081, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d270081, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270082 q = 1) (hb : d270932 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270082, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270082, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270086 q = 1) (hb : d270934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270086, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270086, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68710 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d37298 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270087 q = 1) (hb : d270935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270087, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270087, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d270088 q = 1) (hb : d270936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270088, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270088, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270089 q = 1) (hb : d270937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270089, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270089, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270090 q = 1) (hb : d270938 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270090, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270090, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270096 q = 1) (hb : d270945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270096, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270096, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68711 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37480 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270097 q = 1) (hb : d270946 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270097, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270097, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d270098 q = 1) (hb : d270947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270098, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270098, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270099 q = 1) (hb : d270948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270099, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270099, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270100 q = 1) (hb : d270949 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270100, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270100, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270101 q = 1) (hb : d270950 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270101, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270101, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68713 (p : Pattern) (ha : d270107 p = 1) (hb : d270956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270102 q = 1) (hb : d270951 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270102, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270102, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68712 q ha hb
  have h2 (q : Pattern) (ha : d270103 q = 1) (hb : d270952 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270103, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270103, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270104 q = 1) (hb : d270953 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270104, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270104, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270105 q = 1) (hb : d270954 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270105, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270105, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270106 q = 1) (hb : d270955 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270106, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270106, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270107 q = 1) (hb : d270956 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270107, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270107, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68714 (p : Pattern) (ha : d270198 p = 1) (hb : d271084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37707 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270194 q = 1) (hb : d271080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270194, d271080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270194, d271080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d37864 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d270195 q = 1) (hb : d271081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270195, d271081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270195, d271081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270196 q = 1) (hb : d271082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270196, d271082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270196, d271082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270197 q = 1) (hb : d271083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270197, d271083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270197, d271083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270198 q = 1) (hb : d271084 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270198, d271084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270198, d271084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68715 (p : Pattern) (ha : d270208 p = 1) (hb : d271089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37648 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37657 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d270194 q = 1) (hb : d271080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270194, d271080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270194, d271080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37864 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d270195 q = 1) (hb : d271081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270195, d271081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270195, d271081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270196 q = 1) (hb : d271082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270196, d271082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270196, d271082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270197 q = 1) (hb : d271083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270197, d271083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270197, d271083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d37874 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d37879 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d37882 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d270204 q = 1) (hb : d271085 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270204, d271085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270204, d271085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d37889 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270205 q = 1) (hb : d271086 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270205, d271086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270205, d271086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d270206 q = 1) (hb : d271087 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270206, d271087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270206, d271087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270207 q = 1) (hb : d271088 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270207, d271088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270207, d271088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d270208 q = 1) (hb : d271089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270208, d271089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270208, d271089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68716 (p : Pattern) (ha : d270962 p = 1) (hb : d271096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d37882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270204 q = 1) (hb : d271085 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270204, d271085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270204, d271085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270205 q = 1) (hb : d271086 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270205, d271086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270205, d271086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270206 q = 1) (hb : d271094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270206, d271094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270206, d271094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270207 q = 1) (hb : d271095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270207, d271095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270207, d271095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270962 q = 1) (hb : d271096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270962, d271096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270962, d271096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68717 (p : Pattern) (ha : d270981 p = 1) (hb : d271106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38025 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270976 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270977 q = 1) (hb : d271102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270977, d271102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270977, d271102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270978 q = 1) (hb : d271103 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270978, d271103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270978, d271103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270979 q = 1) (hb : d271104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270979, d271104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270979, d271104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270980 q = 1) (hb : d271105 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270980, d271105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270980, d271105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270981 q = 1) (hb : d271106 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270981, d271106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270981, d271106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68718 (p : Pattern) (ha : d270987 p = 1) (hb : d271112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d37640 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270209 q = 1) (hb : d271090 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270209, d271090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68714 q ha hb
    | true =>
      simp only [d270209, d271090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68715 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37912 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270210 q = 1) (hb : d271091 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270210, d271091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270210, d271091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270960 q = 1) (hb : d271092 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270960, d271092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270960, d271092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270961 q = 1) (hb : d271093 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270961, d271093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270961, d271093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270963 q = 1) (hb : d271097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270963, d271097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270963, d271097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68716 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d37921 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d270964 q = 1) (hb : d271098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270964, d271098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270964, d271098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270965 q = 1) (hb : d271099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270965, d271099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270965, d271099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d270966 q = 1) (hb : d271100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270966, d271100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270966, d271100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d270967 q = 1) (hb : d271101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270967, d271101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270967, d271101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d270982 q = 1) (hb : d271107 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270982, d271107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270982, d271107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68717 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38139 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270983 q = 1) (hb : d271108 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270983, d271108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270983, d271108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d270984 q = 1) (hb : d271109 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270984, d271109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d270984, d271109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d270985 q = 1) (hb : d271110 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270985, d271110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270985, d271110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d270986 q = 1) (hb : d271111 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270986, d271111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270986, d271111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d270987 q = 1) (hb : d271112 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270987, d271112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270987, d271112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68719 (p : Pattern) (ha : d270993 p = 1) (hb : d271118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270988 q = 1) (hb : d271113 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270988, d271113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270988, d271113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68718 q ha hb
  have h2 (q : Pattern) (ha : d270989 q = 1) (hb : d271114 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270989, d271114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270989, d271114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270990 q = 1) (hb : d271115 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270990, d271115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270990, d271115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270991 q = 1) (hb : d271116 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270991, d271116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270991, d271116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270992 q = 1) (hb : d271117 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270992, d271117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270992, d271117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270993 q = 1) (hb : d271118 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270993, d271118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270993, d271118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68720 (p : Pattern) (ha : d270553 p = 1) (hb : d271127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d38329 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270549 q = 1) (hb : d271123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270549, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270549, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d38470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d270550 q = 1) (hb : d271124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270550, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270550, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270551 q = 1) (hb : d271125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270551, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270551, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270552 q = 1) (hb : d271126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270552, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270552, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270553 q = 1) (hb : d271127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270553, d271127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270553, d271127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro68721 (p : Pattern) (ha : d270563 p = 1) (hb : d271132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d270549 q = 1) (hb : d271123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270549, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270549, d271123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d38470 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d270550 q = 1) (hb : d271124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270550, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270550, d271124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270551 q = 1) (hb : d271125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270551, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270551, d271125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270552 q = 1) (hb : d271126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270552, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270552, d271126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d38480 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d38485 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d38488 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d270559 q = 1) (hb : d271128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270559, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270559, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38495 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d270560 q = 1) (hb : d271129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270560, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270560, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d270561 q = 1) (hb : d271130 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270561, d271130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270561, d271130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270562 q = 1) (hb : d271131 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270562, d271131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270562, d271131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d270563 q = 1) (hb : d271132 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270563, d271132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270563, d271132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro68722 (p : Pattern) (ha : d271000 p = 1) (hb : d271139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270559 q = 1) (hb : d271128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270559, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270559, d271128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38495 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270560 q = 1) (hb : d271129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270560, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270560, d271129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270561 q = 1) (hb : d271137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270561, d271137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270561, d271137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270562 q = 1) (hb : d271138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270562, d271138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270562, d271138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271000 q = 1) (hb : d271139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271000, d271139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271000, d271139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68723 (p : Pattern) (ha : d271019 p = 1) (hb : d271149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38617 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271015 q = 1) (hb : d271145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d271015, d271145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271015, d271145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38737 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271016 q = 1) (hb : d271146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d271016, d271146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271016, d271146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271017 q = 1) (hb : d271147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d271017, d271147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271017, d271147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271018 q = 1) (hb : d271148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d271018, d271148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271018, d271148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271019 q = 1) (hb : d271149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d271019, d271149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271019, d271149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro68724 (p : Pattern) (ha : d271025 p = 1) (hb : d271155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d38284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270564 q = 1) (hb : d271133 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270564, d271133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68720 q ha hb
    | true =>
      simp only [d270564, d271133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68721 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38518 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d270565 q = 1) (hb : d271134 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270565, d271134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270565, d271134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d270998 q = 1) (hb : d271135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270998, d271135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270998, d271135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270999 q = 1) (hb : d271136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270999, d271136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270999, d271136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271001 q = 1) (hb : d271140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271001, d271140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271001, d271140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68722 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d38527 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d271002 q = 1) (hb : d271141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271002, d271141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d271002, d271141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271003 q = 1) (hb : d271142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271003, d271142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d271003, d271142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d271004 q = 1) (hb : d271143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271004, d271143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271004, d271143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d271005 q = 1) (hb : d271144 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271005, d271144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271005, d271144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271020 q = 1) (hb : d271150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d271020, d271150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271020, d271150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68723 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d38753 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d271021 q = 1) (hb : d271151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d271021, d271151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d271021, d271151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271022 q = 1) (hb : d271152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271022, d271152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271022, d271152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d271023 q = 1) (hb : d271153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d271023, d271153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d271023, d271153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d271024 q = 1) (hb : d271154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d271024, d271154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d271024, d271154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d271025 q = 1) (hb : d271155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d271025, d271155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d271025, d271155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro68725 (p : Pattern) (ha : d271031 p = 1) (hb : d271161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271026 q = 1) (hb : d271156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d271026, d271156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271026, d271156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68724 q ha hb
  have h2 (q : Pattern) (ha : d271027 q = 1) (hb : d271157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d271027, d271157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271027, d271157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271028 q = 1) (hb : d271158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d271028, d271158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271028, d271158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271029 q = 1) (hb : d271159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d271029, d271159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271029, d271159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271030 q = 1) (hb : d271160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d271030, d271160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271030, d271160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271031 q = 1) (hb : d271161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d271031, d271161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d271031, d271161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro68726 (p : Pattern) (ha : d271037 p = 1) (hb : d271167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d270027 q = 1) (hb : d270902 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270027, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68695 q ha hb
    | true =>
      simp only [d270027, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68701 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270067 q = 1) (hb : d270929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270067, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270067, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68707 q ha hb
  have h3 (q : Pattern) (ha : d270068 q = 1) (hb : d270930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270068, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270068, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270108 q = 1) (hb : d270957 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270108, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270108, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68713 q ha hb
  have h5 (q : Pattern) (ha : d270109 q = 1) (hb : d270958 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270109, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270109, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270110 q = 1) (hb : d270959 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270110, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270110, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270994 q = 1) (hb : d271119 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270994, d271119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270994, d271119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68719 q ha hb
  have h8 (q : Pattern) (ha : d270995 q = 1) (hb : d271120 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270995, d271120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270995, d271120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270996 q = 1) (hb : d271121 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270996, d271121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270996, d271121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270997 q = 1) (hb : d271122 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d270997, d271122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d270997, d271122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271032 q = 1) (hb : d271162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d271032, d271162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271032, d271162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68725 q ha hb
  have h12 (q : Pattern) (ha : d271033 q = 1) (hb : d271163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d271033, d271163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271033, d271163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d271034 q = 1) (hb : d271164 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d271034, d271164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271034, d271164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271035 q = 1) (hb : d271165 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d271035, d271165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271035, d271165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271036 q = 1) (hb : d271166 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d271036, d271166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d271036, d271166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271037 q = 1) (hb : d271167 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d271037, d271167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d271037, d271167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro68727 (p : Pattern) (ha : d271043 p = 1) (hb : d271173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271038 q = 1) (hb : d271168 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d271038, d271168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68726 q ha hb
    | true =>
      simp only [d271038, d271168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271039 q = 1) (hb : d271169 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d271039, d271169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271039, d271169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271040 q = 1) (hb : d271170 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d271040, d271170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271040, d271170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271041 q = 1) (hb : d271171 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d271041, d271171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271041, d271171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271042 q = 1) (hb : d271172 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d271042, d271172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271042, d271172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271043 q = 1) (hb : d271173 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d271043, d271173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271043, d271173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68728 (p : Pattern) (ha : d271049 p = 1) (hb : d271179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271044 q = 1) (hb : d271174 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d271044, d271174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68727 q ha hb
    | true =>
      simp only [d271044, d271174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271045 q = 1) (hb : d271175 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d271045, d271175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271045, d271175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271046 q = 1) (hb : d271176 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d271046, d271176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271046, d271176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271047 q = 1) (hb : d271177 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d271047, d271177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271047, d271177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271048 q = 1) (hb : d271178 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d271048, d271178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271048, d271178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271049 q = 1) (hb : d271179 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d271049, d271179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271049, d271179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68729 (p : Pattern) (ha : d271055 p = 1) (hb : d271185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271050 q = 1) (hb : d271180 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d271050, d271180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68728 q ha hb
    | true =>
      simp only [d271050, d271180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271051 q = 1) (hb : d271181 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d271051, d271181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271051, d271181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271052 q = 1) (hb : d271182 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d271052, d271182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271052, d271182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271053 q = 1) (hb : d271183 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d271053, d271183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271053, d271183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271054 q = 1) (hb : d271184 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d271054, d271184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271054, d271184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271055 q = 1) (hb : d271185 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d271055, d271185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271055, d271185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68730 (p : Pattern) (ha : d271061 p = 1) (hb : d271191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271056 q = 1) (hb : d271186 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d271056, d271186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68729 q ha hb
    | true =>
      simp only [d271056, d271186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271057 q = 1) (hb : d271187 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d271057, d271187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271057, d271187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271058 q = 1) (hb : d271188 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d271058, d271188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271058, d271188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271059 q = 1) (hb : d271189 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d271059, d271189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271059, d271189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271060 q = 1) (hb : d271190 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d271060, d271190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271060, d271190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271061 q = 1) (hb : d271191 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d271061, d271191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271061, d271191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68731 (p : Pattern) (ha : d271067 p = 1) (hb : d271197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271062 q = 1) (hb : d271192 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d271062, d271192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68730 q ha hb
    | true =>
      simp only [d271062, d271192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271063 q = 1) (hb : d271193 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d271063, d271193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271063, d271193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271064 q = 1) (hb : d271194 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d271064, d271194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271064, d271194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271065 q = 1) (hb : d271195 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d271065, d271195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271065, d271195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271066 q = 1) (hb : d271196 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d271066, d271196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271066, d271196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271067 q = 1) (hb : d271197 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d271067, d271197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271067, d271197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68732 (p : Pattern) (ha : d271073 p = 1) (hb : d271203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271068 q = 1) (hb : d271198 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d271068, d271198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68731 q ha hb
    | true =>
      simp only [d271068, d271198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271069 q = 1) (hb : d271199 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d271069, d271199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271069, d271199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271070 q = 1) (hb : d271200 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d271070, d271200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271070, d271200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271071 q = 1) (hb : d271201 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d271071, d271201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271071, d271201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271072 q = 1) (hb : d271202 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d271072, d271202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271072, d271202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271073 q = 1) (hb : d271203 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d271073, d271203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271073, d271203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68733 (p : Pattern) (ha : d271079 p = 1) (hb : d271209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271074 q = 1) (hb : d271204 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d271074, d271204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68732 q ha hb
    | true =>
      simp only [d271074, d271204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271075 q = 1) (hb : d271205 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d271075, d271205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271075, d271205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271076 q = 1) (hb : d271206 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d271076, d271206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271076, d271206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271077 q = 1) (hb : d271207 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d271077, d271207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271077, d271207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271078 q = 1) (hb : d271208 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d271078, d271208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271078, d271208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271079 q = 1) (hb : d271209 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d271079, d271209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271079, d271209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro68734 (p : Pattern) (ha : d18 p = 1) (hb : d271211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d271211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16, d271211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d18, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro68735 (p : Pattern) (ha : d24 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d271211 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68734 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, d271212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d24 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro68736 (p : Pattern) (ha : d30 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68735 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68737 (p : Pattern) (ha : d36 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68736 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68738 (p : Pattern) (ha : d42 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68737 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68739 (p : Pattern) (ha : d48 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68738 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68740 (p : Pattern) (ha : d49 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68737 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68741 (p : Pattern) (ha : d55 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68738 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68740 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68742 (p : Pattern) (ha : d60 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68740 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68743 (p : Pattern) (ha : d71 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68735 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68735 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68744 (p : Pattern) (ha : d77 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68743 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68745 (p : Pattern) (ha : d83 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68744 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68746 (p : Pattern) (ha : d89 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68745 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68747 (p : Pattern) (ha : d95 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68739 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68741 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68742 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68746 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68748 (p : Pattern) (ha : d104 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68738 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
theorem andIntro68749 (p : Pattern) (ha : d111 p = 1) (hb : d271212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68738 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68740 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d271212 q = 1) : d0 q = 1 := by
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
end NetHack.Soko22Hazard87
