import NetHack.Soko22Hazard87.AndIntroBlocks0068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro17250 (p : Pattern) (ha : d99361 p = 1) (hb : d107483 p = 1) : d111615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99356 q = 1) (hb : d107483 q = 1) : d111610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99356, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99356, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17249 q ha hb
  have h2 (q : Pattern) (ha : d99357 q = 1) (hb : d107483 q = 1) : d111611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99357, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99357, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99358 q = 1) (hb : d107483 q = 1) : d111612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99358, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99358, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99359 q = 1) (hb : d107483 q = 1) : d111613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99359, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99359, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99360 q = 1) (hb : d107483 q = 1) : d111614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99360, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99360, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99361 q = 1) (hb : d107483 q = 1) : d111615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99361, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99361, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17251 (p : Pattern) (ha : d99367 p = 1) (hb : d107483 p = 1) : d111621 p = 1 := by
  have h0 (q : Pattern) (ha : d99248 q = 1) (hb : d107483 q = 1) : d111502 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99248, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17230 q ha hb
    | true =>
      simp only [d99248, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17234 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d99275 q = 1) (hb : d107483 q = 1) : d111529 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99275, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99275, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17238 q ha hb
  have h3 (q : Pattern) (ha : d99276 q = 1) (hb : d107483 q = 1) : d111530 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99276, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99276, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99303 q = 1) (hb : d107483 q = 1) : d111557 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99303, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99303, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17242 q ha hb
  have h5 (q : Pattern) (ha : d99304 q = 1) (hb : d107483 q = 1) : d111558 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99304, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99304, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99305 q = 1) (hb : d107483 q = 1) : d111559 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99305, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99305, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d99332 q = 1) (hb : d107483 q = 1) : d111586 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99332, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99332, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17246 q ha hb
  have h8 (q : Pattern) (ha : d99333 q = 1) (hb : d107483 q = 1) : d111587 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99333, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99333, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d99334 q = 1) (hb : d107483 q = 1) : d111588 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99334, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99334, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99335 q = 1) (hb : d107483 q = 1) : d111589 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99335, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99335, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d99362 q = 1) (hb : d107483 q = 1) : d111616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99362, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99362, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17250 q ha hb
  have h12 (q : Pattern) (ha : d99363 q = 1) (hb : d107483 q = 1) : d111617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99363, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99363, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d99364 q = 1) (hb : d107483 q = 1) : d111618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99364, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99364, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d99365 q = 1) (hb : d107483 q = 1) : d111619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99365, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99365, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d99366 q = 1) (hb : d107483 q = 1) : d111620 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d99366, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99366, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d99367 q = 1) (hb : d107483 q = 1) : d111621 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d99367, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d99367, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro17252 (p : Pattern) (ha : d99373 p = 1) (hb : d107483 p = 1) : d111627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99368 q = 1) (hb : d107483 q = 1) : d111622 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d99368, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17251 q ha hb
    | true =>
      simp only [d99368, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99369 q = 1) (hb : d107483 q = 1) : d111623 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d99369, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99369, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99370 q = 1) (hb : d107483 q = 1) : d111624 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d99370, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99370, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99371 q = 1) (hb : d107483 q = 1) : d111625 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d99371, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99371, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99372 q = 1) (hb : d107483 q = 1) : d111626 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d99372, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99372, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99373 q = 1) (hb : d107483 q = 1) : d111627 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d99373, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99373, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17253 (p : Pattern) (ha : d99379 p = 1) (hb : d107483 p = 1) : d111633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99374 q = 1) (hb : d107483 q = 1) : d111628 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d99374, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17252 q ha hb
    | true =>
      simp only [d99374, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99375 q = 1) (hb : d107483 q = 1) : d111629 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d99375, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99375, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99376 q = 1) (hb : d107483 q = 1) : d111630 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d99376, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99376, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99377 q = 1) (hb : d107483 q = 1) : d111631 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d99377, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99377, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99378 q = 1) (hb : d107483 q = 1) : d111632 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d99378, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99378, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99379 q = 1) (hb : d107483 q = 1) : d111633 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d99379, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99379, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17254 (p : Pattern) (ha : d99385 p = 1) (hb : d107483 p = 1) : d111639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99380 q = 1) (hb : d107483 q = 1) : d111634 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d99380, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17253 q ha hb
    | true =>
      simp only [d99380, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99381 q = 1) (hb : d107483 q = 1) : d111635 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d99381, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99381, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99382 q = 1) (hb : d107483 q = 1) : d111636 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d99382, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99382, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99383 q = 1) (hb : d107483 q = 1) : d111637 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d99383, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99383, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99384 q = 1) (hb : d107483 q = 1) : d111638 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d99384, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99384, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99385 q = 1) (hb : d107483 q = 1) : d111639 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d99385, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99385, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17255 (p : Pattern) (ha : d99391 p = 1) (hb : d107483 p = 1) : d111645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99386 q = 1) (hb : d107483 q = 1) : d111640 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d99386, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17254 q ha hb
    | true =>
      simp only [d99386, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99387 q = 1) (hb : d107483 q = 1) : d111641 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d99387, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99387, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99388 q = 1) (hb : d107483 q = 1) : d111642 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d99388, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99388, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99389 q = 1) (hb : d107483 q = 1) : d111643 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d99389, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99389, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99390 q = 1) (hb : d107483 q = 1) : d111644 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d99390, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99390, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99391 q = 1) (hb : d107483 q = 1) : d111645 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d99391, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99391, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17256 (p : Pattern) (ha : d99397 p = 1) (hb : d107483 p = 1) : d111651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99392 q = 1) (hb : d107483 q = 1) : d111646 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d99392, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17255 q ha hb
    | true =>
      simp only [d99392, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99393 q = 1) (hb : d107483 q = 1) : d111647 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d99393, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99393, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99394 q = 1) (hb : d107483 q = 1) : d111648 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d99394, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99394, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99395 q = 1) (hb : d107483 q = 1) : d111649 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d99395, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99395, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99396 q = 1) (hb : d107483 q = 1) : d111650 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d99396, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99396, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99397 q = 1) (hb : d107483 q = 1) : d111651 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d99397, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99397, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17257 (p : Pattern) (ha : d99403 p = 1) (hb : d107483 p = 1) : d111657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99398 q = 1) (hb : d107483 q = 1) : d111652 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d99398, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17256 q ha hb
    | true =>
      simp only [d99398, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99399 q = 1) (hb : d107483 q = 1) : d111653 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d99399, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99399, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99400 q = 1) (hb : d107483 q = 1) : d111654 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d99400, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99400, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99401 q = 1) (hb : d107483 q = 1) : d111655 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d99401, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99401, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99402 q = 1) (hb : d107483 q = 1) : d111656 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d99402, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99402, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99403 q = 1) (hb : d107483 q = 1) : d111657 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d99403, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99403, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17258 (p : Pattern) (ha : d99409 p = 1) (hb : d107483 p = 1) : d111663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99404 q = 1) (hb : d107483 q = 1) : d111658 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d99404, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17257 q ha hb
    | true =>
      simp only [d99404, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d99405 q = 1) (hb : d107483 q = 1) : d111659 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d99405, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99405, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99406 q = 1) (hb : d107483 q = 1) : d111660 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d99406, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99406, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99407 q = 1) (hb : d107483 q = 1) : d111661 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d99407, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99407, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99408 q = 1) (hb : d107483 q = 1) : d111662 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d99408, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99408, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d99409 q = 1) (hb : d107483 q = 1) : d111663 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d99409, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99409, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17259 (p : Pattern) (ha : d107602 p = 1) (hb : d110638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d107592 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107592, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107599 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107599, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107600 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107600, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107601 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107601, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107602 q = 1) (hb : d110638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17260 (p : Pattern) (ha : d107621 p = 1) (hb : d110645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d107592 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107592, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107599 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107599, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107600 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107600, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107601 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107601, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107607 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107611 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107505 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
    | true =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d107614 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107614, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107618 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107618, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107619 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107619, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107620 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107620, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107621 q = 1) (hb : d110645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107621, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17261 (p : Pattern) (ha : d107630 p = 1) (hb : d111453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107505 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
    | true =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107614, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107618 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107628 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107629 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107630 q = 1) (hb : d111453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17262 (p : Pattern) (ha : d107659 p = 1) (hb : d111463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107535 q = 1) (hb : d110617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17057 q ha hb
    | true =>
      simp only [d107535, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d111459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107649, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107656 q = 1) (hb : d111460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107657 q = 1) (hb : d111461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107658 q = 1) (hb : d111462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107659 q = 1) (hb : d111463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17263 (p : Pattern) (ha : d107665 p = 1) (hb : d111469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107622 q = 1) (hb : d110646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17259 q ha hb
    | true =>
      simp only [d107622, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17260 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107625 q = 1) (hb : d110647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107625, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107626 q = 1) (hb : d111451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107626, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107627 q = 1) (hb : d111452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107627, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107631 q = 1) (hb : d111454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107631, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17261 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107632 q = 1) (hb : d111455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107632, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107633 q = 1) (hb : d111456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107633, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107634 q = 1) (hb : d111457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107634, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107635 q = 1) (hb : d111458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107635, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107660 q = 1) (hb : d111464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107660, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17262 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107661 q = 1) (hb : d111465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107661, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107662 q = 1) (hb : d111466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107662, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107663 q = 1) (hb : d111467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107663, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107664 q = 1) (hb : d111468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107664, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107665 q = 1) (hb : d111469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107665, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17264 (p : Pattern) (ha : d107671 p = 1) (hb : d111475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d107547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d107547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16176 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d107548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d107548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d107549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d107549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d107550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d107550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d107551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d107551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107666 q = 1) (hb : d111470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107666, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17263 q ha hb
  have h8 (q : Pattern) (ha : d107667 q = 1) (hb : d111471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107667, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107668 q = 1) (hb : d111472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107668, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107669 q = 1) (hb : d111473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107669, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107670 q = 1) (hb : d111474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107670, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107671 q = 1) (hb : d111475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d107671, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro17265 (p : Pattern) (ha : d107748 p = 1) (hb : d110755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107689 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
    | true =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h5 (q : Pattern) (ha : d107738 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107738, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107745 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107745, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107746 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107746, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107747 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107747, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107748 q = 1) (hb : d110755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17266 (p : Pattern) (ha : d107769 p = 1) (hb : d110764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107689 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
    | true =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h4 (q : Pattern) (ha : d107738 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107738, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107745 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107745, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107746 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107746, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107747 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107747, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107754 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107759 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107699 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17084 q ha hb
    | true =>
      simp only [d107699, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q hb ha
  have h13 (q : Pattern) (ha : d107762 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107762, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107766 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107766, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107767 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107767, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107768 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107768, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107769 q = 1) (hb : d110764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107769, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17267 (p : Pattern) (ha : d107789 p = 1) (hb : d111478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107699 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17084 q ha hb
    | true =>
      simp only [d107699, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q hb ha
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107762, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107766 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107787 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107788 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107789 q = 1) (hb : d111478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17268 (p : Pattern) (ha : d107838 p = 1) (hb : d111489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107827 q = 1) (hb : d111484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107827, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17102 q ha hb
    | true =>
      simp only [d107827, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15946 q hb ha
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d111485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107828, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107835 q = 1) (hb : d111486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107836 q = 1) (hb : d111487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107837 q = 1) (hb : d111488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107838 q = 1) (hb : d111489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17269 (p : Pattern) (ha : d107851 p = 1) (hb : d111495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107707 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107770 q = 1) (hb : d110765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17265 q ha hb
    | true =>
      simp only [d107770, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17266 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107784 q = 1) (hb : d110766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107784, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107785 q = 1) (hb : d111476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107785, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107786 q = 1) (hb : d111477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107786, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107790 q = 1) (hb : d111479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107790, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17267 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107792 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107793 q = 1) (hb : d111480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107793, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107794 q = 1) (hb : d111481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107794, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107795 q = 1) (hb : d111482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107795, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107796 q = 1) (hb : d111483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107796, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107839 q = 1) (hb : d111490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107839, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17268 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107847 q = 1) (hb : d111491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107847, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107848 q = 1) (hb : d111492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107848, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107849 q = 1) (hb : d111493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107849, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d107850 q = 1) (hb : d111494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107850, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d107851 q = 1) (hb : d111495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107851, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17270 (p : Pattern) (ha : d107857 p = 1) (hb : d111501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d111496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17269 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d111497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d111498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d111499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d111500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d111501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17271 (p : Pattern) (ha : d107950 p = 1) (hb : d110883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d107883 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
    | true =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h5 (q : Pattern) (ha : d107932 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107932, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107947 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107947, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107948 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107948, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107949 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107949, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107950 q = 1) (hb : d110883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17272 (p : Pattern) (ha : d107971 p = 1) (hb : d110892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107883 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
    | true =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h4 (q : Pattern) (ha : d107932 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d107932, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d107947 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107947, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107948 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107948, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107949 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107949, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107956 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d107961 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d107893 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17110 q ha hb
    | true =>
      simp only [d107893, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q hb ha
  have h13 (q : Pattern) (ha : d107964 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d107964, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d107968 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107968, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d107969 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d107969, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107970 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d107970, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107971 q = 1) (hb : d110892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107971, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17273 (p : Pattern) (ha : d107991 p = 1) (hb : d111505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107893 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17110 q ha hb
    | true =>
      simp only [d107893, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q hb ha
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107964, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107968 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107989 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107990 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107991 q = 1) (hb : d111505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17274 (p : Pattern) (ha : d108055 p = 1) (hb : d111516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108036 q = 1) (hb : d111511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108036, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17129 q ha hb
    | true =>
      simp only [d108036, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15984 q hb ha
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d111512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108037, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108051 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108052 q = 1) (hb : d111513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108053 q = 1) (hb : d111514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108054 q = 1) (hb : d111515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108055 q = 1) (hb : d111516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17275 (p : Pattern) (ha : d108068 p = 1) (hb : d111522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107901 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107972 q = 1) (hb : d110893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17271 q ha hb
    | true =>
      simp only [d107972, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17272 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107986 q = 1) (hb : d110894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107986, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107987 q = 1) (hb : d111503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107987, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107988 q = 1) (hb : d111504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107988, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107992 q = 1) (hb : d111506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107992, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17273 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107994 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107995 q = 1) (hb : d111507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107995, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107996 q = 1) (hb : d111508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107996, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107997 q = 1) (hb : d111509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107997, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d107998 q = 1) (hb : d111510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107998, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108056 q = 1) (hb : d111517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108056, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17274 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108064 q = 1) (hb : d111518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108064, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108065 q = 1) (hb : d111519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108065, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108066 q = 1) (hb : d111520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108066, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108067 q = 1) (hb : d111521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108067, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108068 q = 1) (hb : d111522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108068, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17276 (p : Pattern) (ha : d108074 p = 1) (hb : d111528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d111523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17275 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d111524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d111525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d111526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d111527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d111528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17277 (p : Pattern) (ha : d108168 p = 1) (hb : d111016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108101 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
    | true =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h5 (q : Pattern) (ha : d108150 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108150, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108165 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108165, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108166 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108166, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108167 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108167, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108168 q = 1) (hb : d111016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17278 (p : Pattern) (ha : d108189 p = 1) (hb : d111025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108101 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
    | true =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h4 (q : Pattern) (ha : d108150 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108150, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108164 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108165 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108165, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108166 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108166, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108167 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108167, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108174 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108179 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108111 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17138 q ha hb
    | true =>
      simp only [d108111, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16018 q hb ha
  have h13 (q : Pattern) (ha : d108182 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108182, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108186 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108186, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108187 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108187, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108188 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108188, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108189 q = 1) (hb : d111025 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108189, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17279 (p : Pattern) (ha : d108209 p = 1) (hb : d111533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108111 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17138 q ha hb
    | true =>
      simp only [d108111, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16018 q hb ha
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108182, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108185 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108186 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108207 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108208 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108209 q = 1) (hb : d111533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17280 (p : Pattern) (ha : d108273 p = 1) (hb : d111544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108254 q = 1) (hb : d111539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108254, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17157 q ha hb
    | true =>
      simp only [d108254, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16024 q hb ha
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d111540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108255, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108269 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108270 q = 1) (hb : d111541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108271 q = 1) (hb : d111542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108272 q = 1) (hb : d111543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108273 q = 1) (hb : d111544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17281 (p : Pattern) (ha : d108286 p = 1) (hb : d111550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108119 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108190 q = 1) (hb : d111026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17277 q ha hb
    | true =>
      simp only [d108190, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17278 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108204 q = 1) (hb : d111027 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108204, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108205 q = 1) (hb : d111531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108205, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108206 q = 1) (hb : d111532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108206, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108210 q = 1) (hb : d111534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108210, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17279 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108212 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108213 q = 1) (hb : d111535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108213, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108214 q = 1) (hb : d111536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108214, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108215 q = 1) (hb : d111537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108215, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108216 q = 1) (hb : d111538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108216, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108274 q = 1) (hb : d111545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108274, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17280 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108281 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108282 q = 1) (hb : d111546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108282, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108283 q = 1) (hb : d111547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108283, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108284 q = 1) (hb : d111548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108284, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108285 q = 1) (hb : d111549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108285, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108286 q = 1) (hb : d111550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108286, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17282 (p : Pattern) (ha : d108292 p = 1) (hb : d111556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d111551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17281 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d111552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d111553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d111554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d111555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d111556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17283 (p : Pattern) (ha : d108387 p = 1) (hb : d111150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108320 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
    | true =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h5 (q : Pattern) (ha : d108369 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108369, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108384 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108384, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108385 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108385, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108386 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108386, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108387 q = 1) (hb : d111150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17284 (p : Pattern) (ha : d108408 p = 1) (hb : d111159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108368 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108320 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
    | true =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h4 (q : Pattern) (ha : d108369 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108369, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108383 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108384 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108384, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108385 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108385, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108386 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108386, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108393 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108398 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108330 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17166 q ha hb
    | true =>
      simp only [d108330, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16058 q hb ha
  have h13 (q : Pattern) (ha : d108401 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108401, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108405 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108405, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108406 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108406, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108407 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108407, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108408 q = 1) (hb : d111159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108408, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17285 (p : Pattern) (ha : d108428 p = 1) (hb : d111562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108330 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17166 q ha hb
    | true =>
      simp only [d108330, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16058 q hb ha
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108401, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108404 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108405 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108426 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108427 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108428 q = 1) (hb : d111562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17286 (p : Pattern) (ha : d108492 p = 1) (hb : d111573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108473 q = 1) (hb : d111568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108473, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17185 q ha hb
    | true =>
      simp only [d108473, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16064 q hb ha
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d111569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108474, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108489 q = 1) (hb : d111570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108490 q = 1) (hb : d111571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108491 q = 1) (hb : d111572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108492 q = 1) (hb : d111573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17287 (p : Pattern) (ha : d108505 p = 1) (hb : d111579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108409 q = 1) (hb : d111160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17283 q ha hb
    | true =>
      simp only [d108409, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17284 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108423 q = 1) (hb : d111161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108423, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108424 q = 1) (hb : d111560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108424, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108425 q = 1) (hb : d111561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108425, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108429 q = 1) (hb : d111563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108429, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17285 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108431 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108432 q = 1) (hb : d111564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108432, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108433 q = 1) (hb : d111565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108433, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108434 q = 1) (hb : d111566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108434, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108435 q = 1) (hb : d111567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108435, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108493 q = 1) (hb : d111574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108493, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17286 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108500 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108501 q = 1) (hb : d111575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108501, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108502 q = 1) (hb : d111576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108502, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108503 q = 1) (hb : d111577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108503, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108504 q = 1) (hb : d111578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108504, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108505 q = 1) (hb : d111579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108505, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17288 (p : Pattern) (ha : d108511 p = 1) (hb : d111585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d111580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17287 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d111581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d111582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d111583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d111584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d111585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17289 (p : Pattern) (ha : d108607 p = 1) (hb : d111285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108540 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
    | true =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h5 (q : Pattern) (ha : d108589 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108589, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108604 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108604, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108605 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108605, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108606 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108606, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108607 q = 1) (hb : d111285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17290 (p : Pattern) (ha : d108628 p = 1) (hb : d111294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108566 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108540 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
    | true =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h4 (q : Pattern) (ha : d108589 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108589, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d108603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108604 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108604, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108605 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108605, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108606 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108606, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d108618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d108550 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17194 q ha hb
    | true =>
      simp only [d108550, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16098 q hb ha
  have h13 (q : Pattern) (ha : d108621 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108621, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108625 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108625, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108626 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108626, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108627 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108627, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108628 q = 1) (hb : d111294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108628, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17291 (p : Pattern) (ha : d108648 p = 1) (hb : d111592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108550 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17194 q ha hb
    | true =>
      simp only [d108550, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16098 q hb ha
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108621, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108625 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108646 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108647 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108648 q = 1) (hb : d111592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17292 (p : Pattern) (ha : d108712 p = 1) (hb : d111603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d108688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108693 q = 1) (hb : d111598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108693, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17213 q ha hb
    | true =>
      simp only [d108693, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16104 q hb ha
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d111599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108694, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d108708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108709 q = 1) (hb : d111600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108710 q = 1) (hb : d111601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108711 q = 1) (hb : d111602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108712 q = 1) (hb : d111603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17293 (p : Pattern) (ha : d108725 p = 1) (hb : d111609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d108558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108629 q = 1) (hb : d111295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17289 q ha hb
    | true =>
      simp only [d108629, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17290 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108643 q = 1) (hb : d111296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108643, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108644 q = 1) (hb : d111590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108644, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108645 q = 1) (hb : d111591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108645, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108649 q = 1) (hb : d111593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108649, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17291 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108652 q = 1) (hb : d111594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108652, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108653 q = 1) (hb : d111595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108653, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d108654 q = 1) (hb : d111596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108654, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d108655 q = 1) (hb : d111597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108655, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108713 q = 1) (hb : d111604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108713, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17292 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d108720 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108721 q = 1) (hb : d111605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108721, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108722 q = 1) (hb : d111606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108722, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d108723 q = 1) (hb : d111607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108723, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d108724 q = 1) (hb : d111608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108724, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d108725 q = 1) (hb : d111609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108725, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17294 (p : Pattern) (ha : d108731 p = 1) (hb : d111615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d111610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17293 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d111611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d111612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d111613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d111614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d111615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17295 (p : Pattern) (ha : d108737 p = 1) (hb : d111621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d111502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17264 q ha hb
    | true =>
      simp only [d107858, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17270 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d111529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17276 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d111530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d111557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17282 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d111558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d111559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d111586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17288 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d111587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d111588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d111589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d111616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17294 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d111617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d111618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d111619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d111620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d111621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17296 (p : Pattern) (ha : d108743 p = 1) (hb : d111627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d111622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17295 q ha hb
    | true =>
      simp only [d108738, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d111623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d111624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d111625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d111626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d111627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17297 (p : Pattern) (ha : d108749 p = 1) (hb : d111633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d111628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17296 q ha hb
    | true =>
      simp only [d108744, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d111629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d111630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d111631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d111632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d111633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17298 (p : Pattern) (ha : d108755 p = 1) (hb : d111639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d111634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17297 q ha hb
    | true =>
      simp only [d108750, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d111635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d111636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d111637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d111638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d111639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17299 (p : Pattern) (ha : d108761 p = 1) (hb : d111645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d111640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17298 q ha hb
    | true =>
      simp only [d108756, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d111641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d111642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d111643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d111644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d111645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17300 (p : Pattern) (ha : d108767 p = 1) (hb : d111651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d111646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17299 q ha hb
    | true =>
      simp only [d108762, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d111647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d111648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d111649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d111650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d111651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17301 (p : Pattern) (ha : d108773 p = 1) (hb : d111657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d111652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17300 q ha hb
    | true =>
      simp only [d108768, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d111653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d111654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d111655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d111656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d111657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17302 (p : Pattern) (ha : d108779 p = 1) (hb : d111663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d111658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17301 q ha hb
    | true =>
      simp only [d108774, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d111659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d111660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d111661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d111662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d111663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17303 (p : Pattern) (ha : d108822 p = 1) (hb : d110638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108818 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108818, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108819 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108819, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108820 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108820, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108821 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108821, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108822 q = 1) (hb : d110638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17304 (p : Pattern) (ha : d108827 p = 1) (hb : d110645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108818 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108818, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10774 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108819 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108819, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108820 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108820, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108821 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108821, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10783 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10787 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108823 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108823, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108824 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108824, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108825 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108825, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108826 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108826, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108827 q = 1) (hb : d110645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108827, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17305 (p : Pattern) (ha : d108834 p = 1) (hb : d111453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108823 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108823, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10795 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108824, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d111453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17306 (p : Pattern) (ha : d108844 p = 1) (hb : d111463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108840 q = 1) (hb : d111459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108840, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10846 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d111460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108841, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d111461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d111462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d111463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17307 (p : Pattern) (ha : d108850 p = 1) (hb : d111469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10729 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108828 q = 1) (hb : d110646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17303 q ha hb
    | true =>
      simp only [d108828, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17304 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108829 q = 1) (hb : d110647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108829, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108830 q = 1) (hb : d111451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108830, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108831 q = 1) (hb : d111452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108831, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108835 q = 1) (hb : d111454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108835, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17305 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108836 q = 1) (hb : d111455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108836, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108837 q = 1) (hb : d111456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108837, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108838 q = 1) (hb : d111457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108838, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108839 q = 1) (hb : d111458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108839, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108845 q = 1) (hb : d111464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108845, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17306 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108846 q = 1) (hb : d111465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108846, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108847 q = 1) (hb : d111466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108847, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108848 q = 1) (hb : d111467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108848, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108849 q = 1) (hb : d111468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108849, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108850 q = 1) (hb : d111469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108850, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17308 (p : Pattern) (ha : d108856 p = 1) (hb : d111475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d108813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16225 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d108814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d108815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d108816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d108817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d111470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17307 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d111471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d111472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d111473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d111474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d111475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d108856, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro17309 (p : Pattern) (ha : d108861 p = 1) (hb : d110755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108857 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108857, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108858 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108858, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108859 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108859, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108860 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108860, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108861 q = 1) (hb : d110755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17310 (p : Pattern) (ha : d108866 p = 1) (hb : d110764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10915 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108857 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108857, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10957 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108858 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108858, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108859 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108859, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108860 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108860, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10967 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10972 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108862 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108862, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108863 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108863, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108864 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108864, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108865 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108865, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108866 q = 1) (hb : d110764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108866, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17311 (p : Pattern) (ha : d108873 p = 1) (hb : d111478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108862 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108862, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108863, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d111478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17312 (p : Pattern) (ha : d108883 p = 1) (hb : d111489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111484 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108879 q = 1) (hb : d111485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108879, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11067 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d111486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108880, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d111487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d111488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d111489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17313 (p : Pattern) (ha : d108889 p = 1) (hb : d111495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10898 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108867 q = 1) (hb : d110765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17309 q ha hb
    | true =>
      simp only [d108867, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17310 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108868 q = 1) (hb : d110766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108868, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108869 q = 1) (hb : d111476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108869, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108870 q = 1) (hb : d111477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108870, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108874 q = 1) (hb : d111479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108874, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17311 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11008 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108875 q = 1) (hb : d111480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108875, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108876 q = 1) (hb : d111481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108876, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108877 q = 1) (hb : d111482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108877, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108878 q = 1) (hb : d111483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108878, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108884 q = 1) (hb : d111490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108884, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17312 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108885 q = 1) (hb : d111491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108885, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108886 q = 1) (hb : d111492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108886, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108887 q = 1) (hb : d111493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108887, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108888 q = 1) (hb : d111494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108888, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108889 q = 1) (hb : d111495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108889, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17314 (p : Pattern) (ha : d108895 p = 1) (hb : d111501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d111496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17313 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d111497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d111498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d111499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d111500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d111501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17315 (p : Pattern) (ha : d108901 p = 1) (hb : d110883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108897 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108897, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108898 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108898, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108899 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108899, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108900 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108900, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108901 q = 1) (hb : d110883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17316 (p : Pattern) (ha : d108906 p = 1) (hb : d110892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11146 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108897 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108897, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11208 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108898 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108898, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108899 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108899, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108900 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108900, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11218 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11223 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108902 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108902, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108903 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108903, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108904 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108904, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108905 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108905, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108906 q = 1) (hb : d110892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108906, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17317 (p : Pattern) (ha : d108913 p = 1) (hb : d111505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108902 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108902, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11232 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108903, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d111505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17318 (p : Pattern) (ha : d108923 p = 1) (hb : d111516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11296 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111511 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108919 q = 1) (hb : d111512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108919, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11336 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d111513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108920, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d111514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d111515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d111516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17319 (p : Pattern) (ha : d108929 p = 1) (hb : d111522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108907 q = 1) (hb : d110893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17315 q ha hb
    | true =>
      simp only [d108907, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17316 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108908 q = 1) (hb : d110894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108908, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108909 q = 1) (hb : d111503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108909, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108910 q = 1) (hb : d111504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108910, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108914 q = 1) (hb : d111506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108914, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17317 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11259 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108915 q = 1) (hb : d111507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108915, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108916 q = 1) (hb : d111508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108916, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108917 q = 1) (hb : d111509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108917, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108918 q = 1) (hb : d111510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108918, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108924 q = 1) (hb : d111517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108924, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17318 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108925 q = 1) (hb : d111518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108925, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108926 q = 1) (hb : d111519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108926, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108927 q = 1) (hb : d111520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108927, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108928 q = 1) (hb : d111521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108928, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108929 q = 1) (hb : d111522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108929, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17320 (p : Pattern) (ha : d108935 p = 1) (hb : d111528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d111523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17319 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d111524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d111525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d111526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d111527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d111528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17321 (p : Pattern) (ha : d108942 p = 1) (hb : d111016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108938 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108938, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108939 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108939, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108940 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108940, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108941 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108941, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108942 q = 1) (hb : d111016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17322 (p : Pattern) (ha : d108947 p = 1) (hb : d111025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11438 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108938 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108938, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11478 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108939 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108939, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108940 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108940, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108941 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108941, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11488 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11493 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108943 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108943, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108944 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108944, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108945 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108945, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108946 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108946, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108947 q = 1) (hb : d111025 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108947, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17323 (p : Pattern) (ha : d108954 p = 1) (hb : d111533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108943 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108943, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11502 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108944, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d111533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17324 (p : Pattern) (ha : d108964 p = 1) (hb : d111544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108960 q = 1) (hb : d111540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108960, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11606 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d111541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108961, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d111542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d111543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d111544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17325 (p : Pattern) (ha : d108970 p = 1) (hb : d111550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11408 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108948 q = 1) (hb : d111026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17321 q ha hb
    | true =>
      simp only [d108948, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17322 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108949 q = 1) (hb : d111027 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108949, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108950 q = 1) (hb : d111531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108950, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108951 q = 1) (hb : d111532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108951, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108955 q = 1) (hb : d111534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108955, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17323 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11529 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108956 q = 1) (hb : d111535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108956, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108957 q = 1) (hb : d111536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108957, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108958 q = 1) (hb : d111537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108958, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d108959 q = 1) (hb : d111538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108959, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108965 q = 1) (hb : d111545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108965, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17324 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11622 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108966 q = 1) (hb : d111546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108966, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108967 q = 1) (hb : d111547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108967, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108968 q = 1) (hb : d111548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108968, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d108969 q = 1) (hb : d111549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108969, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d108970 q = 1) (hb : d111550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108970, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17326 (p : Pattern) (ha : d108976 p = 1) (hb : d111556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d111551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17325 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d111552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d111553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d111554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d111555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d111556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17327 (p : Pattern) (ha : d108984 p = 1) (hb : d111150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108980 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108980, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108981 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108981, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d108982 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108982, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108983 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108983, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108984 q = 1) (hb : d111150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17328 (p : Pattern) (ha : d108989 p = 1) (hb : d111159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d108980 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108980, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d108981 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108981, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d108982 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108982, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108983 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108983, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d108985 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108985, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108986 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108986, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d108987 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108987, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108988 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108988, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108989 q = 1) (hb : d111159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108989, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17329 (p : Pattern) (ha : d108996 p = 1) (hb : d111562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108985 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108985, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108986, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d111562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17330 (p : Pattern) (ha : d109006 p = 1) (hb : d111573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109002 q = 1) (hb : d111569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d111570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109003, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d111571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d111572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d111573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17331 (p : Pattern) (ha : d109012 p = 1) (hb : d111579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108990 q = 1) (hb : d111160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17327 q ha hb
    | true =>
      simp only [d108990, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17328 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108991 q = 1) (hb : d111161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108991, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108992 q = 1) (hb : d111560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108992, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108993 q = 1) (hb : d111561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108993, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108997 q = 1) (hb : d111563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108997, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17329 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108998 q = 1) (hb : d111564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108998, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108999 q = 1) (hb : d111565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108999, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109000 q = 1) (hb : d111566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109000, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109001 q = 1) (hb : d111567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109001, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109007 q = 1) (hb : d111574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109007, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17330 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109008 q = 1) (hb : d111575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109008, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109009 q = 1) (hb : d111576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109009, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109010 q = 1) (hb : d111577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109010, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109011 q = 1) (hb : d111578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109011, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109012 q = 1) (hb : d111579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109012, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17332 (p : Pattern) (ha : d109018 p = 1) (hb : d111585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d111580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17331 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d111581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d111582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d111583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d111584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d111585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17333 (p : Pattern) (ha : d109027 p = 1) (hb : d111285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109023 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d109023, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d109024 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109024, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d109025 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109025, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109026 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109026, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109027 q = 1) (hb : d111285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17334 (p : Pattern) (ha : d109032 p = 1) (hb : d111294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d109023 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109023, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109024 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109024, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d109025 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109025, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109026 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109026, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12031 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12036 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d109028 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d109028, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109029 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109029, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109030 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d109030, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109031 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d109031, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d109032 q = 1) (hb : d111294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109032, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro17335 (p : Pattern) (ha : d109039 p = 1) (hb : d111592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109028 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109028, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109029, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d111592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17336 (p : Pattern) (ha : d109049 p = 1) (hb : d111603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109045 q = 1) (hb : d111599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d111600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109046, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d111601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d111602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d111603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17337 (p : Pattern) (ha : d109055 p = 1) (hb : d111609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109033 q = 1) (hb : d111295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17333 q ha hb
    | true =>
      simp only [d109033, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17334 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109034 q = 1) (hb : d111296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109034, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109035 q = 1) (hb : d111590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109035, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109036 q = 1) (hb : d111591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109036, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109040 q = 1) (hb : d111593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109040, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17335 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d109041 q = 1) (hb : d111594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109041, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d109042 q = 1) (hb : d111595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109042, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109043 q = 1) (hb : d111596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109043, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109044 q = 1) (hb : d111597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109044, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109050 q = 1) (hb : d111604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109050, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17336 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109051 q = 1) (hb : d111605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109051, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109052 q = 1) (hb : d111606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109052, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109053 q = 1) (hb : d111607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109053, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109054 q = 1) (hb : d111608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109054, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109055 q = 1) (hb : d111609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109055, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17338 (p : Pattern) (ha : d109061 p = 1) (hb : d111615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d111610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17337 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d111611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d111612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d111613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d111614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d111615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17339 (p : Pattern) (ha : d109067 p = 1) (hb : d111621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d111502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17308 q ha hb
    | true =>
      simp only [d108896, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17314 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d111529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17320 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d111530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d111557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17326 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d111558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d111559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d111586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17332 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d111587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d111588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d111589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d111616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17338 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d111617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d111618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d111619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d111620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d111621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro17340 (p : Pattern) (ha : d109073 p = 1) (hb : d111627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d111622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17339 q ha hb
    | true =>
      simp only [d109068, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d111623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d111624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d111625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d111626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d111627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17341 (p : Pattern) (ha : d109079 p = 1) (hb : d111633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d111628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17340 q ha hb
    | true =>
      simp only [d109074, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d111629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d111630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d111631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d111632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d111633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17342 (p : Pattern) (ha : d109085 p = 1) (hb : d111639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d111634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17341 q ha hb
    | true =>
      simp only [d109080, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d111635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d111636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d111637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d111638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d111639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17343 (p : Pattern) (ha : d109091 p = 1) (hb : d111645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d111640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17342 q ha hb
    | true =>
      simp only [d109086, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d111641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d111642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d111643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d111644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d111645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17344 (p : Pattern) (ha : d109097 p = 1) (hb : d111651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d111646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17343 q ha hb
    | true =>
      simp only [d109092, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d111647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d111648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d111649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d111650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d111651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17345 (p : Pattern) (ha : d109103 p = 1) (hb : d111657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d111652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17344 q ha hb
    | true =>
      simp only [d109098, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d111653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d111654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d111655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d111656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d111657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17346 (p : Pattern) (ha : d109109 p = 1) (hb : d111663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d111658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17345 q ha hb
    | true =>
      simp only [d109104, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d111659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d111660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d111661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d111662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d111663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17347 (p : Pattern) (ha : d7241 p = 1) (hb : d92315 p = 1) : d481 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d147 q = 1) : d147 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148 q = 1) (hb : d92313 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d92313, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148, d92313, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7240 q = 1) (hb : d92315 q = 1) : d480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7240, d92315, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7240, d92315, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7241 q = 1) (hb : d92315 q = 1) : d481 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7241, d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7241, d481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17348 (p : Pattern) (ha : d7247 p = 1) (hb : d92315 p = 1) : d111667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7246 q = 1) (hb : d92315 q = 1) : d111666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7246, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7247 q = 1) (hb : d92315 q = 1) : d111667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d111667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17349 (p : Pattern) (ha : d85394 p = 1) (hb : d92315 p = 1) : d111673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d92315 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d92315 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7248 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
    | true =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85390 q = 1) (hb : d92315 q = 1) : d111669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85390, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92315 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85391 q = 1) (hb : d92315 q = 1) : d111670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85392 q = 1) (hb : d92315 q = 1) : d111671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85392, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85393 q = 1) (hb : d92315 q = 1) : d111672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85393, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85394 q = 1) (hb : d92315 q = 1) : d111673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85394, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85394, d111673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17350 (p : Pattern) (ha : d7254 p = 1) (hb : d92315 p = 1) : d111674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7246 q = 1) (hb : d92315 q = 1) : d111666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7246, d111666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7254 q = 1) (hb : d92315 q = 1) : d111674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7254, d111674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17351 (p : Pattern) (ha : d85399 p = 1) (hb : d92315 p = 1) : d111680 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d92315 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d92315 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7248 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
    | true =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85390 q = 1) (hb : d92315 q = 1) : d111669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85390, d111669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d92315 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85391 q = 1) (hb : d92315 q = 1) : d111670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d111670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85392 q = 1) (hb : d92315 q = 1) : d111671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85392, d111671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85393 q = 1) (hb : d92315 q = 1) : d111672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85393, d111672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d92315 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d92315 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7255 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17350 q ha hb
    | true =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85395 q = 1) (hb : d92315 q = 1) : d111676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85395, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d92315 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d85396 q = 1) (hb : d92315 q = 1) : d111677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85396, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85397 q = 1) (hb : d92315 q = 1) : d111678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85397, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85397, d111678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85398 q = 1) (hb : d92315 q = 1) : d111679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85398, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85398, d111679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d85399 q = 1) (hb : d92315 q = 1) : d111680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85399, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85399, d111680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro17352 (p : Pattern) (ha : d85406 p = 1) (hb : d92315 p = 1) : d111687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17350 q ha hb
    | true =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85395 q = 1) (hb : d92315 q = 1) : d111676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85395, d111676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d92315 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85396 q = 1) (hb : d92315 q = 1) : d111677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85396, d111677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85404 q = 1) (hb : d92315 q = 1) : d111685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85404, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85404, d111685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85405 q = 1) (hb : d92315 q = 1) : d111686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85405, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85405, d111686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85406 q = 1) (hb : d92315 q = 1) : d111687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85406, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85406, d111687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17353 (p : Pattern) (ha : d7274 p = 1) (hb : d92315 p = 1) : d683 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d234 q = 1) : d234 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d235 q = 1) (hb : d92313 q = 1) : d673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d92313, d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d235, d92313, d673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7273 q = 1) (hb : d92315 q = 1) : d682 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7273, d92315, d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7273, d92315, d682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7274 q = 1) (hb : d92315 q = 1) : d683 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7274, d683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7274, d683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17354 (p : Pattern) (ha : d7280 p = 1) (hb : d92315 p = 1) : d111696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d92315 q = 1) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17353 q ha hb
    | true =>
      simp only [d7275, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d92315 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7277 q = 1) (hb : d92315 q = 1) : d111693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7277, d111693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7278 q = 1) (hb : d92315 q = 1) : d111694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7278, d111694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7279 q = 1) (hb : d92315 q = 1) : d111695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7279, d111695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7280 q = 1) (hb : d92315 q = 1) : d111696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7280, d111696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17355 (p : Pattern) (ha : d85416 p = 1) (hb : d92315 p = 1) : d111702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92315 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d92315 q = 1) : d111697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17354 q ha hb
    | true =>
      simp only [d7281, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85412 q = 1) (hb : d92315 q = 1) : d111698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85412, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85412, d111698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d92315 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85413 q = 1) (hb : d92315 q = 1) : d111699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85413, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85413, d111699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85414 q = 1) (hb : d92315 q = 1) : d111700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85414, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85414, d111700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85415 q = 1) (hb : d92315 q = 1) : d111701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85415, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85415, d111701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85416 q = 1) (hb : d92315 q = 1) : d111702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85416, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85416, d111702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17356 (p : Pattern) (ha : d85422 p = 1) (hb : d92315 p = 1) : d111708 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d92315 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85400 q = 1) (hb : d92315 q = 1) : d111681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85400, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17349 q ha hb
    | true =>
      simp only [d85400, d111681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17351 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d92315 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85401 q = 1) (hb : d92315 q = 1) : d111682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85401, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85401, d111682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85402 q = 1) (hb : d92315 q = 1) : d111683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85402, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85402, d111683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85403 q = 1) (hb : d92315 q = 1) : d111684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85403, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85403, d111684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85407 q = 1) (hb : d92315 q = 1) : d111688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85407, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85407, d111688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17352 q ha hb
  have h8 (q : Pattern) (ha : d85408 q = 1) (hb : d92315 q = 1) : d111689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85408, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85408, d111689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d85409 q = 1) (hb : d92315 q = 1) : d111690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85409, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85409, d111690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d85410 q = 1) (hb : d92315 q = 1) : d111691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85410, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85410, d111691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85411 q = 1) (hb : d92315 q = 1) : d111692 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85411, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85411, d111692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85417 q = 1) (hb : d92315 q = 1) : d111703 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85417, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85417, d111703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17355 q ha hb
  have h13 (q : Pattern) (ha : d85418 q = 1) (hb : d92315 q = 1) : d111704 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85418, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85418, d111704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d85419 q = 1) (hb : d92315 q = 1) : d111705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85419, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85419, d111705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d85420 q = 1) (hb : d92315 q = 1) : d111706 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85420, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85420, d111706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d85421 q = 1) (hb : d92315 q = 1) : d111707 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85421, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85421, d111707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85422 q = 1) (hb : d92315 q = 1) : d111708 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85422, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85422, d111708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17357 (p : Pattern) (ha : d7302 p = 1) (hb : d92315 p = 1) : d111718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
    | true =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d92315 q = 1) : d111714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d92315 q = 1) : d111715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d92315 q = 1) : d111716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d92315 q = 1) : d111717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7302 q = 1) (hb : d92315 q = 1) : d111718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17358 (p : Pattern) (ha : d7309 p = 1) (hb : d92315 p = 1) : d111725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
    | true =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d92315 q = 1) : d111714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d92315 q = 1) : d111715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d92315 q = 1) : d111716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d92315 q = 1) : d111717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7255 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17350 q ha hb
    | true =>
      simp only [d7255, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7305 q = 1) (hb : d92315 q = 1) : d111721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7306 q = 1) (hb : d92315 q = 1) : d111722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7306, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7307 q = 1) (hb : d92315 q = 1) : d111723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7308 q = 1) (hb : d92315 q = 1) : d111724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7309 q = 1) (hb : d92315 q = 1) : d111725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7309, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro17359 (p : Pattern) (ha : d7376 p = 1) (hb : d92315 p = 1) : d111770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d92315 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d92315 q = 1) : d111668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
    | true =>
      simp only [d7248, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d92315 q = 1) : d111714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d92315 q = 1) : d111715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d92315 q = 1) : d111716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d92315 q = 1) : d111717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d92315 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7376 q = 1) (hb : d92315 q = 1) : d111770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7376, d111770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17360 (p : Pattern) (ha : d7314 p = 1) (hb : d92315 p = 1) : d111730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7313 q = 1) (hb : d92315 q = 1) : d111729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7314 q = 1) (hb : d92315 q = 1) : d111730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d111730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17361 (p : Pattern) (ha : d7321 p = 1) (hb : d92315 p = 1) : d111737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7319 q = 1) (hb : d92315 q = 1) : d111735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7320 q = 1) (hb : d92315 q = 1) : d111736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7320, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7321 q = 1) (hb : d92315 q = 1) : d111737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d111737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17362 (p : Pattern) (ha : d7326 p = 1) (hb : d92315 p = 1) : d98845 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d327 q = 1) : d327 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d328 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d328, d92313, d6797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7325 q = 1) (hb : d92315 q = 1) : d98844 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7325, d92315, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7325, d92315, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7326 q = 1) (hb : d92315 q = 1) : d98845 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7326, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7326, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17363 (p : Pattern) (ha : d7332 p = 1) (hb : d92315 p = 1) : d111744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7332 q = 1) (hb : d92315 q = 1) : d111744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7332, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17364 (p : Pattern) (ha : d7347 p = 1) (hb : d92315 p = 1) : d491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d92315 q = 1) : d488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d92315 q = 1) : d489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d92315 q = 1) : d490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7347 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, d491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17365 (p : Pattern) (ha : d85432 p = 1) (hb : d92315 p = 1) : d111751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92315 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d92315 q = 1) : d111731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17360 q ha hb
    | true =>
      simp only [d7315, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d92315 q = 1) : d111732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d92315 q = 1) : d111733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d92315 q = 1) : d111734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92315 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d92315 q = 1) : d111738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17361 q ha hb
    | true =>
      simp only [d7322, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d92315 q = 1) : d111739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d92315 q = 1) : d111740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d92315 q = 1) : d111745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17363 q ha hb
    | true =>
      simp only [d7333, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
  have h11 (q : Pattern) (ha : d85428 q = 1) (hb : d92315 q = 1) : d111746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85428, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7348 q = 1) (hb : d92315 q = 1) : d633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17364 q ha hb
    | true =>
      simp only [d7348, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7349 q = 1) (hb : d92315 q = 1) : d111747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7349, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85429 q = 1) (hb : d92315 q = 1) : d111748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85430 q = 1) (hb : d92315 q = 1) : d111749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85430, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85431 q = 1) (hb : d92315 q = 1) : d111750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85431, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85432 q = 1) (hb : d92315 q = 1) : d111751 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85432, d111751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17366 (p : Pattern) (ha : d7354 p = 1) (hb : d92315 p = 1) : d111752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7245 q = 1) (hb : d92315 q = 1) : d111665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7245, d111665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7313 q = 1) (hb : d92315 q = 1) : d111729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d111729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7354 q = 1) (hb : d92315 q = 1) : d111752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7354, d111752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17367 (p : Pattern) (ha : d7359 p = 1) (hb : d92315 p = 1) : d111757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d92315 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7244 q = 1) (hb : d92315 q = 1) : d111664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d111664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7319 q = 1) (hb : d92315 q = 1) : d111735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d111735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7320 q = 1) (hb : d92315 q = 1) : d111736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7320, d111736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7359 q = 1) (hb : d92315 q = 1) : d111757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7359, d111757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17368 (p : Pattern) (ha : d7363 p = 1) (hb : d92315 p = 1) : d111761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7329 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7329, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7330 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7330, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7331 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7331, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7363 q = 1) (hb : d92315 q = 1) : d111761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7363, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17369 (p : Pattern) (ha : d7368 p = 1) (hb : d92315 p = 1) : d501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d92315 q = 1) : d482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17347 q ha hb
    | true =>
      simp only [d7242, d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d92315 q = 1) : d488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7344, d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d92315 q = 1) : d489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d92315 q = 1) : d490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7368 q = 1) (hb : d92315 q = 1) : d501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7368, d501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17370 (p : Pattern) (ha : d85437 p = 1) (hb : d92315 p = 1) : d111768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d92315 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d92315 q = 1) : d111731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17360 q ha hb
    | true =>
      simp only [d7315, d111731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d92315 q = 1) : d111732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d111732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d92315 q = 1) : d111733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d111733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d92315 q = 1) : d111734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d111734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d92315 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d92315 q = 1) : d111738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17361 q ha hb
    | true =>
      simp only [d7322, d111738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d92315 q = 1) : d111739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d111739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d92315 q = 1) : d111740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d111740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d92315 q = 1) : d111745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17363 q ha hb
    | true =>
      simp only [d7333, d111745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17348 q ha hb
  have h11 (q : Pattern) (ha : d85428 q = 1) (hb : d92315 q = 1) : d111746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85428, d111746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7348 q = 1) (hb : d92315 q = 1) : d633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17364 q ha hb
    | true =>
      simp only [d7348, d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7349 q = 1) (hb : d92315 q = 1) : d111747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7349, d111747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85429 q = 1) (hb : d92315 q = 1) : d111748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d111748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85430 q = 1) (hb : d92315 q = 1) : d111749 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85430, d111749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85431 q = 1) (hb : d92315 q = 1) : d111750 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85431, d111750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d92315 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7355 q = 1) (hb : d92315 q = 1) : d111753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17366 q ha hb
    | true =>
      simp only [d7355, d111753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7356 q = 1) (hb : d92315 q = 1) : d111754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d111754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7357 q = 1) (hb : d92315 q = 1) : d111755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7357, d111755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7358 q = 1) (hb : d92315 q = 1) : d111756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d111756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d92315 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7360 q = 1) (hb : d92315 q = 1) : d111758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17367 q ha hb
    | true =>
      simp only [d7360, d111758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7361 q = 1) (hb : d92315 q = 1) : d111759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d111759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7362 q = 1) (hb : d92315 q = 1) : d111760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7362, d111760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7364 q = 1) (hb : d92315 q = 1) : d111762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17368 q ha hb
    | true =>
      simp only [d7364, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17350 q ha hb
  have h27 (q : Pattern) (ha : d85433 q = 1) (hb : d92315 q = 1) : d111763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85433, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7369 q = 1) (hb : d92315 q = 1) : d639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17369 q ha hb
    | true =>
      simp only [d7369, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7370 q = 1) (hb : d92315 q = 1) : d111764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7370, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85434 q = 1) (hb : d92315 q = 1) : d111765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85434, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85435 q = 1) (hb : d92315 q = 1) : d111766 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85435, d111766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85436 q = 1) (hb : d92315 q = 1) : d111767 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85436, d111767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85437 q = 1) (hb : d92315 q = 1) : d111768 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85437, d111768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro17371 (p : Pattern) (ha : d85444 p = 1) (hb : d92315 p = 1) : d111777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7364 q = 1) (hb : d92315 q = 1) : d111762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17368 q ha hb
    | true =>
      simp only [d7364, d111762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17350 q ha hb
  have h2 (q : Pattern) (ha : d85433 q = 1) (hb : d92315 q = 1) : d111763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85433, d111763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7369 q = 1) (hb : d92315 q = 1) : d639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17369 q ha hb
    | true =>
      simp only [d7369, d639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7370 q = 1) (hb : d92315 q = 1) : d111764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7370, d111764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85434 q = 1) (hb : d92315 q = 1) : d111765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85434, d111765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85442 q = 1) (hb : d92315 q = 1) : d111775 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85442, d111775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85443 q = 1) (hb : d92315 q = 1) : d111776 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85443, d111776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d92315 q = 1) : d111777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d111777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17372 (p : Pattern) (ha : d7390 p = 1) (hb : d92315 p = 1) : d98878 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d420 q = 1) : d420 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d421 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d421, d92313, d6843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7389 q = 1) (hb : d92315 q = 1) : d98877 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7389, d92315, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7389, d92315, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7390 q = 1) (hb : d92315 q = 1) : d98878 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7390, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7390, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17373 (p : Pattern) (ha : d7396 p = 1) (hb : d92315 p = 1) : d111786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17372 q ha hb
    | true =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7275 q = 1) (hb : d92315 q = 1) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17353 q ha hb
    | true =>
      simp only [d7275, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7276 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7393 q = 1) (hb : d92315 q = 1) : d111783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7393, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7394 q = 1) (hb : d92315 q = 1) : d111784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7394, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7395 q = 1) (hb : d92315 q = 1) : d111785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7395, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7396 q = 1) (hb : d92315 q = 1) : d111786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7396, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17374 (p : Pattern) (ha : d7411 p = 1) (hb : d92315 p = 1) : d730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d92315 q = 1) : d684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17353 q ha hb
    | true =>
      simp only [d7275, d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7408 q = 1) (hb : d92315 q = 1) : d727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7408, d727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7409 q = 1) (hb : d92315 q = 1) : d728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7409, d728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7410 q = 1) (hb : d92315 q = 1) : d729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7410, d729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7411 q = 1) (hb : d92315 q = 1) : d730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7411, d730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17375 (p : Pattern) (ha : d85454 p = 1) (hb : d92315 p = 1) : d111793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7397 q = 1) (hb : d92315 q = 1) : d111787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17373 q ha hb
    | true =>
      simp only [d7397, d111787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17354 q ha hb
  have h2 (q : Pattern) (ha : d85450 q = 1) (hb : d92315 q = 1) : d111788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85450, d111788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7412 q = 1) (hb : d92315 q = 1) : d731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17374 q ha hb
    | true =>
      simp only [d7412, d731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7413 q = 1) (hb : d92315 q = 1) : d111789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7413, d111789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d92315 q = 1) : d111790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85451, d111790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d92315 q = 1) : d111791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d111791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d92315 q = 1) : d111792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d111792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d92315 q = 1) : d111793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d111793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17376 (p : Pattern) (ha : d85460 p = 1) (hb : d92315 p = 1) : d111799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d92315 q = 1) : d111719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d111719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17357 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d92315 q = 1) : d111720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d111720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d92315 q = 1) : d111726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17357 q ha hb
    | true =>
      simp only [d7310, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17358 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d92315 q = 1) : d111727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d92315 q = 1) : d111728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d111728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85438 q = 1) (hb : d92315 q = 1) : d111769 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17365 q ha hb
    | true =>
      simp only [d85438, d111769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17370 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d92315 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7377 q = 1) (hb : d92315 q = 1) : d111771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17359 q ha hb
    | true =>
      simp only [d7377, d111771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85439 q = 1) (hb : d92315 q = 1) : d111772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85439, d111772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85440 q = 1) (hb : d92315 q = 1) : d111773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85440, d111773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85441 q = 1) (hb : d92315 q = 1) : d111774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85441, d111774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85445 q = 1) (hb : d92315 q = 1) : d111778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85445, d111778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17371 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d92315 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85446 q = 1) (hb : d92315 q = 1) : d111779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85446, d111779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85447 q = 1) (hb : d92315 q = 1) : d111780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85447, d111780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85448 q = 1) (hb : d92315 q = 1) : d111781 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85448, d111781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85449 q = 1) (hb : d92315 q = 1) : d111782 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85449, d111782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85455 q = 1) (hb : d92315 q = 1) : d111794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85455, d111794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17375 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d92315 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85456 q = 1) (hb : d92315 q = 1) : d111795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85456, d111795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85457 q = 1) (hb : d92315 q = 1) : d111796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85457, d111796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85458 q = 1) (hb : d92315 q = 1) : d111797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85458, d111797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85459 q = 1) (hb : d92315 q = 1) : d111798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85459, d111798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85460 q = 1) (hb : d92315 q = 1) : d111799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85460, d111799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro17377 (p : Pattern) (ha : d85466 p = 1) (hb : d92315 p = 1) : d111805 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d92315 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85423 q = 1) (hb : d92315 q = 1) : d111709 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85423, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85423, d111709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17356 q ha hb
  have h3 (q : Pattern) (ha : d85424 q = 1) (hb : d92315 q = 1) : d111710 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85424, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85424, d111710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85425 q = 1) (hb : d92315 q = 1) : d111711 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85425, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85425, d111711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85426 q = 1) (hb : d92315 q = 1) : d111712 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85426, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85426, d111712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85427 q = 1) (hb : d92315 q = 1) : d111713 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85427, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85427, d111713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d92315 q = 1) : d111800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d111800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17376 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d92315 q = 1) : d111801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d111801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d92315 q = 1) : d111802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d111802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d92315 q = 1) : d111803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d111803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d92315 q = 1) : d111804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d111804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d92315 q = 1) : d111805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85466, d111805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro17378 (p : Pattern) (ha : d7433 p = 1) (hb : d92315 p = 1) : d111744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7430 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7431 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7432 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7432, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7433 q = 1) (hb : d92315 q = 1) : d111744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d111744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17379 (p : Pattern) (ha : d7439 p = 1) (hb : d92315 p = 1) : d111811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d92315 q = 1) : d111806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17378 q ha hb
    | true =>
      simp only [d7434, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d92315 q = 1) : d111807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d92315 q = 1) : d111808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d92315 q = 1) : d111809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d92315 q = 1) : d111810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7439 q = 1) (hb : d92315 q = 1) : d111811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17380 (p : Pattern) (ha : d7442 p = 1) (hb : d92315 p = 1) : d111761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7430 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7431 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7432 q = 1) (hb : d92315 q = 1) : d111743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7432, d111743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7442 q = 1) (hb : d92315 q = 1) : d111761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7442, d111761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17381 (p : Pattern) (ha : d7448 p = 1) (hb : d92315 p = 1) : d111819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d92315 q = 1) : d111806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17378 q ha hb
    | true =>
      simp only [d7434, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d92315 q = 1) : d111807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d92315 q = 1) : d111808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d92315 q = 1) : d111809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d92315 q = 1) : d111810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d92315 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7443 q = 1) (hb : d92315 q = 1) : d111814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17380 q ha hb
    | true =>
      simp only [d7443, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7444 q = 1) (hb : d92315 q = 1) : d111815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7445 q = 1) (hb : d92315 q = 1) : d111816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7445, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7446 q = 1) (hb : d92315 q = 1) : d111817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7447 q = 1) (hb : d92315 q = 1) : d111818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7448 q = 1) (hb : d92315 q = 1) : d111819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7448, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro17382 (p : Pattern) (ha : d7515 p = 1) (hb : d92315 p = 1) : d111875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d92315 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d92315 q = 1) : d111806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17378 q ha hb
    | true =>
      simp only [d7434, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d92315 q = 1) : d111807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d92315 q = 1) : d111808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d92315 q = 1) : d111809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d92315 q = 1) : d111810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d92315 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7515 q = 1) (hb : d92315 q = 1) : d111875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7515, d111875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17383 (p : Pattern) (ha : d7453 p = 1) (hb : d92315 p = 1) : d111824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7430 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7431 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7452 q = 1) (hb : d92315 q = 1) : d111823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7453 q = 1) (hb : d92315 q = 1) : d111824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d111824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17384 (p : Pattern) (ha : d7460 p = 1) (hb : d92315 p = 1) : d111831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7430 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7458 q = 1) (hb : d92315 q = 1) : d111829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7459 q = 1) (hb : d92315 q = 1) : d111830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7459, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7460 q = 1) (hb : d92315 q = 1) : d111831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d111831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17385 (p : Pattern) (ha : d7465 p = 1) (hb : d92315 p = 1) : d111836 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d551 q = 1) : d551 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d552 q = 1) (hb : d92313 q = 1) : d8451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d552, d92313, d8451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d552, d92313, d8451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7464 q = 1) (hb : d92315 q = 1) : d111835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7464, d92315, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7464, d92315, d111835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7465 q = 1) (hb : d92315 q = 1) : d111836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7465, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7465, d111836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17386 (p : Pattern) (ha : d7471 p = 1) (hb : d92315 p = 1) : d111842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d92315 q = 1) : d111837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17385 q ha hb
    | true =>
      simp only [d7466, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d92315 q = 1) : d111838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d92315 q = 1) : d111839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d92315 q = 1) : d111840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d92315 q = 1) : d111841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7471 q = 1) (hb : d92315 q = 1) : d111842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7471, d111842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17387 (p : Pattern) (ha : d7486 p = 1) (hb : d92315 p = 1) : d111848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d92315 q = 1) : d111845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d92315 q = 1) : d111846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d92315 q = 1) : d111847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7486 q = 1) (hb : d92315 q = 1) : d111848 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, d111848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17388 (p : Pattern) (ha : d85471 p = 1) (hb : d92315 p = 1) : d111854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92315 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7454 q = 1) (hb : d92315 q = 1) : d111825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17383 q ha hb
    | true =>
      simp only [d7454, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7455 q = 1) (hb : d92315 q = 1) : d111826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7456 q = 1) (hb : d92315 q = 1) : d111827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7456, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7457 q = 1) (hb : d92315 q = 1) : d111828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92315 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7461 q = 1) (hb : d92315 q = 1) : d111832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17384 q ha hb
    | true =>
      simp only [d7461, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7462 q = 1) (hb : d92315 q = 1) : d111833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7463 q = 1) (hb : d92315 q = 1) : d111834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7463, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7472 q = 1) (hb : d92315 q = 1) : d111843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17386 q ha hb
    | true =>
      simp only [d7472, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17378 q ha hb
  have h11 (q : Pattern) (ha : d85467 q = 1) (hb : d92315 q = 1) : d111844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85467, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7487 q = 1) (hb : d92315 q = 1) : d111849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17387 q ha hb
    | true =>
      simp only [d7487, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7488 q = 1) (hb : d92315 q = 1) : d111850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7488, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85468 q = 1) (hb : d92315 q = 1) : d111851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85468, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85469 q = 1) (hb : d92315 q = 1) : d111852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85469, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85470 q = 1) (hb : d92315 q = 1) : d111853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85470, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85471 q = 1) (hb : d92315 q = 1) : d111854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85471, d111854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17389 (p : Pattern) (ha : d7493 p = 1) (hb : d92315 p = 1) : d111855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7430 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7431 q = 1) (hb : d92315 q = 1) : d111742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7431, d111742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7452 q = 1) (hb : d92315 q = 1) : d111823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d111823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7493 q = 1) (hb : d92315 q = 1) : d111855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7493, d111855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17390 (p : Pattern) (ha : d7498 p = 1) (hb : d92315 p = 1) : d111860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7430 q = 1) (hb : d92315 q = 1) : d111741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d111741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7458 q = 1) (hb : d92315 q = 1) : d111829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d111829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7459 q = 1) (hb : d92315 q = 1) : d111830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7459, d111830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7498 q = 1) (hb : d92315 q = 1) : d111860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7498, d111860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17391 (p : Pattern) (ha : d7502 p = 1) (hb : d92315 p = 1) : d111864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d92315 q = 1) : d111837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17385 q ha hb
    | true =>
      simp only [d7466, d111837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d92315 q = 1) : d111838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d111838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7468 q = 1) (hb : d92315 q = 1) : d111839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7468, d111839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7469 q = 1) (hb : d92315 q = 1) : d111840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7469, d111840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7470 q = 1) (hb : d92315 q = 1) : d111841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7470, d111841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7502 q = 1) (hb : d92315 q = 1) : d111864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7502, d111864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17392 (p : Pattern) (ha : d7507 p = 1) (hb : d92315 p = 1) : d111867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17362 q ha hb
    | true =>
      simp only [d7327, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d92315 q = 1) : d111845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7483, d111845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d92315 q = 1) : d111846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, d111846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d92315 q = 1) : d111847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, d111847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7507 q = 1) (hb : d92315 q = 1) : d111867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7507, d111867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17393 (p : Pattern) (ha : d85476 p = 1) (hb : d92315 p = 1) : d111873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d92315 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7454 q = 1) (hb : d92315 q = 1) : d111825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17383 q ha hb
    | true =>
      simp only [d7454, d111825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7455 q = 1) (hb : d92315 q = 1) : d111826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d111826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7456 q = 1) (hb : d92315 q = 1) : d111827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7456, d111827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7457 q = 1) (hb : d92315 q = 1) : d111828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d111828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d92315 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7461 q = 1) (hb : d92315 q = 1) : d111832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17384 q ha hb
    | true =>
      simp only [d7461, d111832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7462 q = 1) (hb : d92315 q = 1) : d111833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d111833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7463 q = 1) (hb : d92315 q = 1) : d111834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7463, d111834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7472 q = 1) (hb : d92315 q = 1) : d111843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17386 q ha hb
    | true =>
      simp only [d7472, d111843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17378 q ha hb
  have h11 (q : Pattern) (ha : d85467 q = 1) (hb : d92315 q = 1) : d111844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85467, d111844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7487 q = 1) (hb : d92315 q = 1) : d111849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17387 q ha hb
    | true =>
      simp only [d7487, d111849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7488 q = 1) (hb : d92315 q = 1) : d111850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7488, d111850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85468 q = 1) (hb : d92315 q = 1) : d111851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85468, d111851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85469 q = 1) (hb : d92315 q = 1) : d111852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85469, d111852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85470 q = 1) (hb : d92315 q = 1) : d111853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85470, d111853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d610 q = 1) (hb : d92315 q = 1) : d610 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7494 q = 1) (hb : d92315 q = 1) : d111856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17389 q ha hb
    | true =>
      simp only [d7494, d111856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7495 q = 1) (hb : d92315 q = 1) : d111857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d111857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7496 q = 1) (hb : d92315 q = 1) : d111858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7496, d111858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7497 q = 1) (hb : d92315 q = 1) : d111859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d111859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d616 q = 1) (hb : d92315 q = 1) : d616 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7499 q = 1) (hb : d92315 q = 1) : d111861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17390 q ha hb
    | true =>
      simp only [d7499, d111861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7500 q = 1) (hb : d92315 q = 1) : d111862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d111862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7501 q = 1) (hb : d92315 q = 1) : d111863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7501, d111863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7503 q = 1) (hb : d92315 q = 1) : d111865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17391 q ha hb
    | true =>
      simp only [d7503, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17380 q ha hb
  have h27 (q : Pattern) (ha : d85472 q = 1) (hb : d92315 q = 1) : d111866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85472, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7508 q = 1) (hb : d92315 q = 1) : d111868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17392 q ha hb
    | true =>
      simp only [d7508, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7509 q = 1) (hb : d92315 q = 1) : d111869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7509, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85473 q = 1) (hb : d92315 q = 1) : d111870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85473, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85474 q = 1) (hb : d92315 q = 1) : d111871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85474, d111871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85475 q = 1) (hb : d92315 q = 1) : d111872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85475, d111872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85476 q = 1) (hb : d92315 q = 1) : d111873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85476, d111873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro17394 (p : Pattern) (ha : d85483 p = 1) (hb : d92315 p = 1) : d111882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7503 q = 1) (hb : d92315 q = 1) : d111865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17391 q ha hb
    | true =>
      simp only [d7503, d111865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17380 q ha hb
  have h2 (q : Pattern) (ha : d85472 q = 1) (hb : d92315 q = 1) : d111866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85472, d111866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7508 q = 1) (hb : d92315 q = 1) : d111868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17392 q ha hb
    | true =>
      simp only [d7508, d111868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7509 q = 1) (hb : d92315 q = 1) : d111869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7509, d111869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85473 q = 1) (hb : d92315 q = 1) : d111870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85473, d111870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85481 q = 1) (hb : d92315 q = 1) : d111880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85481, d111880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85482 q = 1) (hb : d92315 q = 1) : d111881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85482, d111881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d92315 q = 1) : d111882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d111882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17395 (p : Pattern) (ha : d7529 p = 1) (hb : d92315 p = 1) : d111889 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d667 q = 1) : d667 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d668 q = 1) (hb : d92313 q = 1) : d8527 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d668, d92313, d8527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d668, d92313, d8527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7528 q = 1) (hb : d92315 q = 1) : d111888 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7528, d92315, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7528, d92315, d111888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7529 q = 1) (hb : d92315 q = 1) : d111889 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7529, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7529, d111889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17396 (p : Pattern) (ha : d7535 p = 1) (hb : d92315 p = 1) : d111895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7530 q = 1) (hb : d92315 q = 1) : d111890 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17395 q ha hb
    | true =>
      simp only [d7530, d111890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7531 q = 1) (hb : d92315 q = 1) : d111891 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7531, d111891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7391 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17372 q ha hb
    | true =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7392 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7532 q = 1) (hb : d92315 q = 1) : d111892 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7532, d111892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7533 q = 1) (hb : d92315 q = 1) : d111893 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7533, d111893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7534 q = 1) (hb : d92315 q = 1) : d111894 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7534, d111894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7535 q = 1) (hb : d92315 q = 1) : d111895 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7535, d111895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17397 (p : Pattern) (ha : d7539 p = 1) (hb : d92315 p = 1) : d111786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17372 q ha hb
    | true =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7536 q = 1) (hb : d92315 q = 1) : d111783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7536, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7537 q = 1) (hb : d92315 q = 1) : d111784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7537, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7538 q = 1) (hb : d92315 q = 1) : d111785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7538, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7539 q = 1) (hb : d92315 q = 1) : d111786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7539, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17398 (p : Pattern) (ha : d7554 p = 1) (hb : d92315 p = 1) : d111901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17372 q ha hb
    | true =>
      simp only [d7391, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7551 q = 1) (hb : d92315 q = 1) : d111898 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7551, d111898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7552 q = 1) (hb : d92315 q = 1) : d111899 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7552, d111899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7553 q = 1) (hb : d92315 q = 1) : d111900 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7553, d111900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7554 q = 1) (hb : d92315 q = 1) : d111901 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7554, d111901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17399 (p : Pattern) (ha : d85493 p = 1) (hb : d92315 p = 1) : d111907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7540 q = 1) (hb : d92315 q = 1) : d111896 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17396 q ha hb
    | true =>
      simp only [d7540, d111896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17397 q ha hb
  have h2 (q : Pattern) (ha : d85489 q = 1) (hb : d92315 q = 1) : d111897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85489, d111897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7555 q = 1) (hb : d92315 q = 1) : d111902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17398 q ha hb
    | true =>
      simp only [d7555, d111902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7556 q = 1) (hb : d92315 q = 1) : d111903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7556, d111903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d92315 q = 1) : d111904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85490, d111904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d92315 q = 1) : d111905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d111905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d92315 q = 1) : d111906 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d111906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d92315 q = 1) : d111907 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d111907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17400 (p : Pattern) (ha : d85499 p = 1) (hb : d92315 p = 1) : d111913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d92315 q = 1) : d111812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d111812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17379 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d92315 q = 1) : d111813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d111813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d92315 q = 1) : d111820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17379 q ha hb
    | true =>
      simp only [d7449, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17381 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d92315 q = 1) : d111821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d92315 q = 1) : d111822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d111822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85477 q = 1) (hb : d92315 q = 1) : d111874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17388 q ha hb
    | true =>
      simp only [d85477, d111874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17393 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d92315 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7516 q = 1) (hb : d92315 q = 1) : d111876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17382 q ha hb
    | true =>
      simp only [d7516, d111876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85478 q = 1) (hb : d92315 q = 1) : d111877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85478, d111877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85479 q = 1) (hb : d92315 q = 1) : d111878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85479, d111878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85480 q = 1) (hb : d92315 q = 1) : d111879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85480, d111879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85484 q = 1) (hb : d92315 q = 1) : d111883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85484, d111883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17394 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d92315 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85485 q = 1) (hb : d92315 q = 1) : d111884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85485, d111884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85486 q = 1) (hb : d92315 q = 1) : d111885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85486, d111885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85487 q = 1) (hb : d92315 q = 1) : d111886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85487, d111886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85488 q = 1) (hb : d92315 q = 1) : d111887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85488, d111887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85494 q = 1) (hb : d92315 q = 1) : d111908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85494, d111908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17399 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d92315 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85495 q = 1) (hb : d92315 q = 1) : d111909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85495, d111909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85496 q = 1) (hb : d92315 q = 1) : d111910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85496, d111910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85497 q = 1) (hb : d92315 q = 1) : d111911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85497, d111911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85498 q = 1) (hb : d92315 q = 1) : d111912 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85498, d111912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85499 q = 1) (hb : d92315 q = 1) : d111913 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85499, d111913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro17401 (p : Pattern) (ha : d85505 p = 1) (hb : d92315 p = 1) : d111919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d92315 q = 1) : d111914 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d111914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17400 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d92315 q = 1) : d111915 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d111915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d92315 q = 1) : d111916 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d111916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d92315 q = 1) : d111917 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d111917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d92315 q = 1) : d111918 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d111918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d92315 q = 1) : d111919 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d111919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17402 (p : Pattern) (ha : d7575 p = 1) (hb : d92315 p = 1) : d98905 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d761 q = 1) : d761 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d765 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d766 q = 1) (hb : d92313 q = 1) : d6875 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d766, d92313, d6875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7574 q = 1) (hb : d92315 q = 1) : d98904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7574, d92315, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7574, d92315, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7575 q = 1) (hb : d92315 q = 1) : d98905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7575, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7575, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17403 (p : Pattern) (ha : d7581 p = 1) (hb : d92315 p = 1) : d111924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7578 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7579 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7580 q = 1) (hb : d92315 q = 1) : d111923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7580, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7581 q = 1) (hb : d92315 q = 1) : d111924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d111924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17404 (p : Pattern) (ha : d7587 p = 1) (hb : d92315 p = 1) : d111930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92315 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d92315 q = 1) : d111925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17403 q ha hb
    | true =>
      simp only [d7582, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d92315 q = 1) : d111926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d92315 q = 1) : d111927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d92315 q = 1) : d111928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d92315 q = 1) : d111929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7587 q = 1) (hb : d92315 q = 1) : d111930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17405 (p : Pattern) (ha : d7590 p = 1) (hb : d92315 p = 1) : d111933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7578 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7579 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7580 q = 1) (hb : d92315 q = 1) : d111923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7580, d111923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7590 q = 1) (hb : d92315 q = 1) : d111933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7590, d111933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17406 (p : Pattern) (ha : d7596 p = 1) (hb : d92315 p = 1) : d111939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92315 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d92315 q = 1) : d111925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17403 q ha hb
    | true =>
      simp only [d7582, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d92315 q = 1) : d111926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d92315 q = 1) : d111927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d92315 q = 1) : d111928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d92315 q = 1) : d111929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d92315 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7591 q = 1) (hb : d92315 q = 1) : d111934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17405 q ha hb
    | true =>
      simp only [d7591, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7592 q = 1) (hb : d92315 q = 1) : d111935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7593 q = 1) (hb : d92315 q = 1) : d111936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7593, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7594 q = 1) (hb : d92315 q = 1) : d111937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7595 q = 1) (hb : d92315 q = 1) : d111938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7596 q = 1) (hb : d92315 q = 1) : d111939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7596, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro17407 (p : Pattern) (ha : d7663 p = 1) (hb : d92315 p = 1) : d111995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d92315 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d92315 q = 1) : d111925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17403 q ha hb
    | true =>
      simp only [d7582, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d92315 q = 1) : d111926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d92315 q = 1) : d111927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d92315 q = 1) : d111928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d92315 q = 1) : d111929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d92315 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7663 q = 1) (hb : d92315 q = 1) : d111995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7663, d111995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17408 (p : Pattern) (ha : d7601 p = 1) (hb : d92315 p = 1) : d111944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7578 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7579 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7600 q = 1) (hb : d92315 q = 1) : d111943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7601 q = 1) (hb : d92315 q = 1) : d111944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d111944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17409 (p : Pattern) (ha : d7608 p = 1) (hb : d92315 p = 1) : d111951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7578 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7606 q = 1) (hb : d92315 q = 1) : d111949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7607 q = 1) (hb : d92315 q = 1) : d111950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7607, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7608 q = 1) (hb : d92315 q = 1) : d111951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d111951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17410 (p : Pattern) (ha : d7613 p = 1) (hb : d92315 p = 1) : d111956 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d842 q = 1) : d842 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d843 q = 1) (hb : d92313 q = 1) : d8613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d92313, d8613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d843, d92313, d8613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7612 q = 1) (hb : d92315 q = 1) : d111955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7612, d92315, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7612, d92315, d111955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7613 q = 1) (hb : d92315 q = 1) : d111956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7613, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7613, d111956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17411 (p : Pattern) (ha : d7619 p = 1) (hb : d92315 p = 1) : d111962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d92315 q = 1) : d111957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17410 q ha hb
    | true =>
      simp only [d7614, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d92315 q = 1) : d111958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d92315 q = 1) : d111959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d92315 q = 1) : d111960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d92315 q = 1) : d111961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7619 q = 1) (hb : d92315 q = 1) : d111962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7619, d111962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17412 (p : Pattern) (ha : d7634 p = 1) (hb : d92315 p = 1) : d111968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d92315 q = 1) : d111965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7631, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d92315 q = 1) : d111966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d92315 q = 1) : d111967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7634 q = 1) (hb : d92315 q = 1) : d111968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7634, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7634, d111968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17413 (p : Pattern) (ha : d85511 p = 1) (hb : d92315 p = 1) : d111974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92315 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7602 q = 1) (hb : d92315 q = 1) : d111945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17408 q ha hb
    | true =>
      simp only [d7602, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7603 q = 1) (hb : d92315 q = 1) : d111946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7604 q = 1) (hb : d92315 q = 1) : d111947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7604, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7605 q = 1) (hb : d92315 q = 1) : d111948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92315 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7609 q = 1) (hb : d92315 q = 1) : d111952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17409 q ha hb
    | true =>
      simp only [d7609, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7610 q = 1) (hb : d92315 q = 1) : d111953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7611 q = 1) (hb : d92315 q = 1) : d111954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7611, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7620 q = 1) (hb : d92315 q = 1) : d111963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17411 q ha hb
    | true =>
      simp only [d7620, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17403 q ha hb
  have h11 (q : Pattern) (ha : d85507 q = 1) (hb : d92315 q = 1) : d111964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85507, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7635 q = 1) (hb : d92315 q = 1) : d111969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17412 q ha hb
    | true =>
      simp only [d7635, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7636 q = 1) (hb : d92315 q = 1) : d111970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7636, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85508 q = 1) (hb : d92315 q = 1) : d111971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85508, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85509 q = 1) (hb : d92315 q = 1) : d111972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85509, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85510 q = 1) (hb : d92315 q = 1) : d111973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85510, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85511 q = 1) (hb : d92315 q = 1) : d111974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85511, d111974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17414 (p : Pattern) (ha : d7641 p = 1) (hb : d92315 p = 1) : d111975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7578 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7579 q = 1) (hb : d92315 q = 1) : d111922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7579, d111922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7600 q = 1) (hb : d92315 q = 1) : d111943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d111943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7641 q = 1) (hb : d92315 q = 1) : d111975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7641, d111975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17415 (p : Pattern) (ha : d7646 p = 1) (hb : d92315 p = 1) : d111980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7578 q = 1) (hb : d92315 q = 1) : d111921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d111921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7606 q = 1) (hb : d92315 q = 1) : d111949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d111949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7607 q = 1) (hb : d92315 q = 1) : d111950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7607, d111950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7646 q = 1) (hb : d92315 q = 1) : d111980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7646, d111980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17416 (p : Pattern) (ha : d7650 p = 1) (hb : d92315 p = 1) : d111984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d92315 q = 1) : d111957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17410 q ha hb
    | true =>
      simp only [d7614, d111957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d92315 q = 1) : d111958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d111958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7616 q = 1) (hb : d92315 q = 1) : d111959 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7616, d111959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7617 q = 1) (hb : d92315 q = 1) : d111960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7617, d111960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7618 q = 1) (hb : d92315 q = 1) : d111961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7618, d111961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7650 q = 1) (hb : d92315 q = 1) : d111984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7650, d111984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17417 (p : Pattern) (ha : d7655 p = 1) (hb : d92315 p = 1) : d111987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17402 q ha hb
    | true =>
      simp only [d7576, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d92315 q = 1) : d111965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7631, d111965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d92315 q = 1) : d111966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, d111966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d92315 q = 1) : d111967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, d111967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7655 q = 1) (hb : d92315 q = 1) : d111987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7655, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7655, d111987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17418 (p : Pattern) (ha : d85516 p = 1) (hb : d92315 p = 1) : d111993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d92315 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7602 q = 1) (hb : d92315 q = 1) : d111945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17408 q ha hb
    | true =>
      simp only [d7602, d111945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7603 q = 1) (hb : d92315 q = 1) : d111946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d111946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7604 q = 1) (hb : d92315 q = 1) : d111947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7604, d111947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7605 q = 1) (hb : d92315 q = 1) : d111948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d111948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d92315 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7609 q = 1) (hb : d92315 q = 1) : d111952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17409 q ha hb
    | true =>
      simp only [d7609, d111952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7610 q = 1) (hb : d92315 q = 1) : d111953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d111953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7611 q = 1) (hb : d92315 q = 1) : d111954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7611, d111954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7620 q = 1) (hb : d92315 q = 1) : d111963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17411 q ha hb
    | true =>
      simp only [d7620, d111963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17403 q ha hb
  have h11 (q : Pattern) (ha : d85507 q = 1) (hb : d92315 q = 1) : d111964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85507, d111964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7635 q = 1) (hb : d92315 q = 1) : d111969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17412 q ha hb
    | true =>
      simp only [d7635, d111969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7636 q = 1) (hb : d92315 q = 1) : d111970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7636, d111970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85508 q = 1) (hb : d92315 q = 1) : d111971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85508, d111971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85509 q = 1) (hb : d92315 q = 1) : d111972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85509, d111972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85510 q = 1) (hb : d92315 q = 1) : d111973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85510, d111973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d916 q = 1) (hb : d92315 q = 1) : d916 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7642 q = 1) (hb : d92315 q = 1) : d111976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17414 q ha hb
    | true =>
      simp only [d7642, d111976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7643 q = 1) (hb : d92315 q = 1) : d111977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d111977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7644 q = 1) (hb : d92315 q = 1) : d111978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7644, d111978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7645 q = 1) (hb : d92315 q = 1) : d111979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d111979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d922 q = 1) (hb : d92315 q = 1) : d922 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7647 q = 1) (hb : d92315 q = 1) : d111981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17415 q ha hb
    | true =>
      simp only [d7647, d111981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7648 q = 1) (hb : d92315 q = 1) : d111982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d111982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7649 q = 1) (hb : d92315 q = 1) : d111983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7649, d111983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7651 q = 1) (hb : d92315 q = 1) : d111985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17416 q ha hb
    | true =>
      simp only [d7651, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17405 q ha hb
  have h27 (q : Pattern) (ha : d85512 q = 1) (hb : d92315 q = 1) : d111986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85512, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7656 q = 1) (hb : d92315 q = 1) : d111988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17417 q ha hb
    | true =>
      simp only [d7656, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7657 q = 1) (hb : d92315 q = 1) : d111989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7657, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85513 q = 1) (hb : d92315 q = 1) : d111990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85513, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85514 q = 1) (hb : d92315 q = 1) : d111991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85514, d111991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85515 q = 1) (hb : d92315 q = 1) : d111992 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85515, d111992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85516 q = 1) (hb : d92315 q = 1) : d111993 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85516, d111993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro17419 (p : Pattern) (ha : d85523 p = 1) (hb : d92315 p = 1) : d112002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7651 q = 1) (hb : d92315 q = 1) : d111985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17416 q ha hb
    | true =>
      simp only [d7651, d111985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17405 q ha hb
  have h2 (q : Pattern) (ha : d85512 q = 1) (hb : d92315 q = 1) : d111986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85512, d111986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7656 q = 1) (hb : d92315 q = 1) : d111988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17417 q ha hb
    | true =>
      simp only [d7656, d111988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7657 q = 1) (hb : d92315 q = 1) : d111989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7657, d111989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85513 q = 1) (hb : d92315 q = 1) : d111990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85513, d111990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85521 q = 1) (hb : d92315 q = 1) : d112000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85521, d112000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85522 q = 1) (hb : d92315 q = 1) : d112001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85522, d112001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d92315 q = 1) : d112002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d112002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17420 (p : Pattern) (ha : d7677 p = 1) (hb : d92315 p = 1) : d112009 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d979 q = 1) : d979 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d984 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d985 q = 1) (hb : d92313 q = 1) : d8689 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d92313, d8689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d985, d92313, d8689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7676 q = 1) (hb : d92315 q = 1) : d112008 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7676, d92315, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7676, d92315, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7677 q = 1) (hb : d92315 q = 1) : d112009 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7677, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7677, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17421 (p : Pattern) (ha : d7681 p = 1) (hb : d92315 p = 1) : d98938 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d984 q = 1) : d984 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d990 q = 1) (hb : d92313 q = 1) : d6921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d990, d92313, d6921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7680 q = 1) (hb : d92315 q = 1) : d98937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7680, d92315, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7680, d92315, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7681 q = 1) (hb : d92315 q = 1) : d98938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7681, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7681, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17422 (p : Pattern) (ha : d7687 p = 1) (hb : d92315 p = 1) : d112015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7678 q = 1) (hb : d92315 q = 1) : d112010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17420 q ha hb
    | true =>
      simp only [d7678, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7679 q = 1) (hb : d92315 q = 1) : d112011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7679, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7682 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17421 q ha hb
    | true =>
      simp only [d7682, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7683 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7684 q = 1) (hb : d92315 q = 1) : d112012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7684, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7685 q = 1) (hb : d92315 q = 1) : d112013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7685, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7686 q = 1) (hb : d92315 q = 1) : d112014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7686, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7687 q = 1) (hb : d92315 q = 1) : d112015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7687, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17423 (p : Pattern) (ha : d7691 p = 1) (hb : d92315 p = 1) : d112019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17421 q ha hb
    | true =>
      simp only [d7682, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d92315 q = 1) : d1007 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7688 q = 1) (hb : d92315 q = 1) : d112016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7688, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7689 q = 1) (hb : d92315 q = 1) : d112017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7689, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7690 q = 1) (hb : d92315 q = 1) : d112018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7690, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7691 q = 1) (hb : d92315 q = 1) : d112019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7691, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17424 (p : Pattern) (ha : d7706 p = 1) (hb : d92315 p = 1) : d112025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17421 q ha hb
    | true =>
      simp only [d7682, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7703 q = 1) (hb : d92315 q = 1) : d112022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7703, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7703, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7704 q = 1) (hb : d92315 q = 1) : d112023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7704, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7704, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7705 q = 1) (hb : d92315 q = 1) : d112024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7705, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7705, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7706 q = 1) (hb : d92315 q = 1) : d112025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7706, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7706, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17425 (p : Pattern) (ha : d85533 p = 1) (hb : d92315 p = 1) : d112031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7692 q = 1) (hb : d92315 q = 1) : d112020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17422 q ha hb
    | true =>
      simp only [d7692, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17423 q ha hb
  have h2 (q : Pattern) (ha : d85529 q = 1) (hb : d92315 q = 1) : d112021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85529, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7707 q = 1) (hb : d92315 q = 1) : d112026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17424 q ha hb
    | true =>
      simp only [d7707, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7708 q = 1) (hb : d92315 q = 1) : d112027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7708, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d92315 q = 1) : d112028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85530, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d92315 q = 1) : d112029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d92315 q = 1) : d112030 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d92315 q = 1) : d112031 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17426 (p : Pattern) (ha : d85539 p = 1) (hb : d92315 p = 1) : d112037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d92315 q = 1) : d111931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17404 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d92315 q = 1) : d111932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d92315 q = 1) : d111940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17404 q ha hb
    | true =>
      simp only [d7597, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17406 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d92315 q = 1) : d111941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d92315 q = 1) : d111942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85517 q = 1) (hb : d92315 q = 1) : d111994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17413 q ha hb
    | true =>
      simp only [d85517, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17418 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d92315 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7664 q = 1) (hb : d92315 q = 1) : d111996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17407 q ha hb
    | true =>
      simp only [d7664, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85518 q = 1) (hb : d92315 q = 1) : d111997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85518, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85519 q = 1) (hb : d92315 q = 1) : d111998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85519, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85520 q = 1) (hb : d92315 q = 1) : d111999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85520, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85524 q = 1) (hb : d92315 q = 1) : d112003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85524, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17419 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d92315 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85525 q = 1) (hb : d92315 q = 1) : d112004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85525, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85526 q = 1) (hb : d92315 q = 1) : d112005 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85526, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85527 q = 1) (hb : d92315 q = 1) : d112006 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85527, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85528 q = 1) (hb : d92315 q = 1) : d112007 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85528, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85534 q = 1) (hb : d92315 q = 1) : d112032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85534, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17425 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d92315 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85535 q = 1) (hb : d92315 q = 1) : d112033 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85535, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85536 q = 1) (hb : d92315 q = 1) : d112034 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85536, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85537 q = 1) (hb : d92315 q = 1) : d112035 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85537, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85538 q = 1) (hb : d92315 q = 1) : d112036 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85538, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85539 q = 1) (hb : d92315 q = 1) : d112037 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85539, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro17427 (p : Pattern) (ha : d85545 p = 1) (hb : d92315 p = 1) : d112043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d92315 q = 1) : d112038 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17426 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d92315 q = 1) : d112039 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d92315 q = 1) : d112040 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d92315 q = 1) : d112041 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d92315 q = 1) : d112042 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d92315 q = 1) : d112043 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17428 (p : Pattern) (ha : d7728 p = 1) (hb : d92315 p = 1) : d98966 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1131 q = 1) : d1131 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1145 q = 1) (hb : d92313 q = 1) : d6954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1145, d92313, d6954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7727 q = 1) (hb : d92315 q = 1) : d98965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7727, d92315, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7727, d92315, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7728 q = 1) (hb : d92315 q = 1) : d98966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7728, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7728, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17429 (p : Pattern) (ha : d7734 p = 1) (hb : d92315 p = 1) : d112049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7731 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7732 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7733 q = 1) (hb : d92315 q = 1) : d112048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7733, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7734 q = 1) (hb : d92315 q = 1) : d112049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17430 (p : Pattern) (ha : d7740 p = 1) (hb : d92315 p = 1) : d112055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92315 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d92315 q = 1) : d112050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17429 q ha hb
    | true =>
      simp only [d7735, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d92315 q = 1) : d112051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d92315 q = 1) : d112052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d92315 q = 1) : d112053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d92315 q = 1) : d112054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7740 q = 1) (hb : d92315 q = 1) : d112055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17431 (p : Pattern) (ha : d7743 p = 1) (hb : d92315 p = 1) : d112058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7731 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7732 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7733 q = 1) (hb : d92315 q = 1) : d112048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7733, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7743 q = 1) (hb : d92315 q = 1) : d112058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7743, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17432 (p : Pattern) (ha : d7749 p = 1) (hb : d92315 p = 1) : d112064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92315 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d92315 q = 1) : d112050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17429 q ha hb
    | true =>
      simp only [d7735, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d92315 q = 1) : d112051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d92315 q = 1) : d112052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d92315 q = 1) : d112053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d92315 q = 1) : d112054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d92315 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7744 q = 1) (hb : d92315 q = 1) : d112059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17431 q ha hb
    | true =>
      simp only [d7744, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7745 q = 1) (hb : d92315 q = 1) : d112060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7746 q = 1) (hb : d92315 q = 1) : d112061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7746, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7747 q = 1) (hb : d92315 q = 1) : d112062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7748 q = 1) (hb : d92315 q = 1) : d112063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7749 q = 1) (hb : d92315 q = 1) : d112064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7749, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro17433 (p : Pattern) (ha : d7816 p = 1) (hb : d92315 p = 1) : d112120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d92315 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d92315 q = 1) : d112050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17429 q ha hb
    | true =>
      simp only [d7735, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d92315 q = 1) : d112051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d92315 q = 1) : d112052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d92315 q = 1) : d112053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d92315 q = 1) : d112054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d92315 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7816 q = 1) (hb : d92315 q = 1) : d112120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7816, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17434 (p : Pattern) (ha : d7754 p = 1) (hb : d92315 p = 1) : d112069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7731 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7732 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7753 q = 1) (hb : d92315 q = 1) : d112068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7754 q = 1) (hb : d92315 q = 1) : d112069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17435 (p : Pattern) (ha : d7761 p = 1) (hb : d92315 p = 1) : d112076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7731 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7759 q = 1) (hb : d92315 q = 1) : d112074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7760 q = 1) (hb : d92315 q = 1) : d112075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7760, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7761 q = 1) (hb : d92315 q = 1) : d112076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17436 (p : Pattern) (ha : d7766 p = 1) (hb : d92315 p = 1) : d112081 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1218 q = 1) : d1218 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1219 q = 1) (hb : d92313 q = 1) : d8780 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d92313, d8780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1219, d92313, d8780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7765 q = 1) (hb : d92315 q = 1) : d112080 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7765, d92315, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7765, d92315, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7766 q = 1) (hb : d92315 q = 1) : d112081 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7766, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7766, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17437 (p : Pattern) (ha : d7772 p = 1) (hb : d92315 p = 1) : d112087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d92315 q = 1) : d112082 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17436 q ha hb
    | true =>
      simp only [d7767, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d92315 q = 1) : d112083 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d92315 q = 1) : d112084 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d92315 q = 1) : d112085 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d92315 q = 1) : d112086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7772 q = 1) (hb : d92315 q = 1) : d112087 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7772, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17438 (p : Pattern) (ha : d7787 p = 1) (hb : d92315 p = 1) : d112093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d92315 q = 1) : d112090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7784, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d92315 q = 1) : d112091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d92315 q = 1) : d112092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7787 q = 1) (hb : d92315 q = 1) : d112093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7787, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7787, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17439 (p : Pattern) (ha : d85552 p = 1) (hb : d92315 p = 1) : d112099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92315 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7755 q = 1) (hb : d92315 q = 1) : d112070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17434 q ha hb
    | true =>
      simp only [d7755, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7756 q = 1) (hb : d92315 q = 1) : d112071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7757 q = 1) (hb : d92315 q = 1) : d112072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7757, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7758 q = 1) (hb : d92315 q = 1) : d112073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92315 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7762 q = 1) (hb : d92315 q = 1) : d112077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17435 q ha hb
    | true =>
      simp only [d7762, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7763 q = 1) (hb : d92315 q = 1) : d112078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7764 q = 1) (hb : d92315 q = 1) : d112079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7764, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7773 q = 1) (hb : d92315 q = 1) : d112088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17437 q ha hb
    | true =>
      simp only [d7773, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17429 q ha hb
  have h11 (q : Pattern) (ha : d85548 q = 1) (hb : d92315 q = 1) : d112089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85548, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7788 q = 1) (hb : d92315 q = 1) : d112094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17438 q ha hb
    | true =>
      simp only [d7788, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7789 q = 1) (hb : d92315 q = 1) : d112095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7789, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85549 q = 1) (hb : d92315 q = 1) : d112096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85549, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85550 q = 1) (hb : d92315 q = 1) : d112097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85550, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85551 q = 1) (hb : d92315 q = 1) : d112098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85551, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85552 q = 1) (hb : d92315 q = 1) : d112099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85552, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17440 (p : Pattern) (ha : d7794 p = 1) (hb : d92315 p = 1) : d112100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7731 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7732 q = 1) (hb : d92315 q = 1) : d112047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7732, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7753 q = 1) (hb : d92315 q = 1) : d112068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7794 q = 1) (hb : d92315 q = 1) : d112100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7794, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17441 (p : Pattern) (ha : d7799 p = 1) (hb : d92315 p = 1) : d112105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7731 q = 1) (hb : d92315 q = 1) : d112046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7759 q = 1) (hb : d92315 q = 1) : d112074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7760 q = 1) (hb : d92315 q = 1) : d112075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7760, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7799 q = 1) (hb : d92315 q = 1) : d112105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7799, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17442 (p : Pattern) (ha : d7803 p = 1) (hb : d92315 p = 1) : d112109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d92315 q = 1) : d112082 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17436 q ha hb
    | true =>
      simp only [d7767, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d92315 q = 1) : d112083 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7769 q = 1) (hb : d92315 q = 1) : d112084 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7769, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7770 q = 1) (hb : d92315 q = 1) : d112085 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7770, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7771 q = 1) (hb : d92315 q = 1) : d112086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7771, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7803 q = 1) (hb : d92315 q = 1) : d112109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7803, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17443 (p : Pattern) (ha : d7808 p = 1) (hb : d92315 p = 1) : d112112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17428 q ha hb
    | true =>
      simp only [d7729, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d92315 q = 1) : d112090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7784, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d92315 q = 1) : d112091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d92315 q = 1) : d112092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7808 q = 1) (hb : d92315 q = 1) : d112112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7808, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7808, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17444 (p : Pattern) (ha : d85557 p = 1) (hb : d92315 p = 1) : d112118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d92315 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7755 q = 1) (hb : d92315 q = 1) : d112070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17434 q ha hb
    | true =>
      simp only [d7755, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7756 q = 1) (hb : d92315 q = 1) : d112071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7757 q = 1) (hb : d92315 q = 1) : d112072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7757, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7758 q = 1) (hb : d92315 q = 1) : d112073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d92315 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7762 q = 1) (hb : d92315 q = 1) : d112077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17435 q ha hb
    | true =>
      simp only [d7762, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7763 q = 1) (hb : d92315 q = 1) : d112078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7764 q = 1) (hb : d92315 q = 1) : d112079 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7764, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7773 q = 1) (hb : d92315 q = 1) : d112088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17437 q ha hb
    | true =>
      simp only [d7773, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17429 q ha hb
  have h11 (q : Pattern) (ha : d85548 q = 1) (hb : d92315 q = 1) : d112089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85548, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7788 q = 1) (hb : d92315 q = 1) : d112094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17438 q ha hb
    | true =>
      simp only [d7788, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7789 q = 1) (hb : d92315 q = 1) : d112095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7789, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85549 q = 1) (hb : d92315 q = 1) : d112096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85549, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85550 q = 1) (hb : d92315 q = 1) : d112097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85550, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85551 q = 1) (hb : d92315 q = 1) : d112098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85551, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1327 q = 1) (hb : d92315 q = 1) : d1327 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7795 q = 1) (hb : d92315 q = 1) : d112101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17440 q ha hb
    | true =>
      simp only [d7795, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7796 q = 1) (hb : d92315 q = 1) : d112102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7797 q = 1) (hb : d92315 q = 1) : d112103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7797, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7798 q = 1) (hb : d92315 q = 1) : d112104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1333 q = 1) (hb : d92315 q = 1) : d1333 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7800 q = 1) (hb : d92315 q = 1) : d112106 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17441 q ha hb
    | true =>
      simp only [d7800, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7801 q = 1) (hb : d92315 q = 1) : d112107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7802 q = 1) (hb : d92315 q = 1) : d112108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7802, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7804 q = 1) (hb : d92315 q = 1) : d112110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17442 q ha hb
    | true =>
      simp only [d7804, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17431 q ha hb
  have h27 (q : Pattern) (ha : d85553 q = 1) (hb : d92315 q = 1) : d112111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85553, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7809 q = 1) (hb : d92315 q = 1) : d112113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17443 q ha hb
    | true =>
      simp only [d7809, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7810 q = 1) (hb : d92315 q = 1) : d112114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7810, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85554 q = 1) (hb : d92315 q = 1) : d112115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85554, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85555 q = 1) (hb : d92315 q = 1) : d112116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85555, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85556 q = 1) (hb : d92315 q = 1) : d112117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85556, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85557 q = 1) (hb : d92315 q = 1) : d112118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85557, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro17445 (p : Pattern) (ha : d85564 p = 1) (hb : d92315 p = 1) : d112127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7804 q = 1) (hb : d92315 q = 1) : d112110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17442 q ha hb
    | true =>
      simp only [d7804, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17431 q ha hb
  have h2 (q : Pattern) (ha : d85553 q = 1) (hb : d92315 q = 1) : d112111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85553, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7809 q = 1) (hb : d92315 q = 1) : d112113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17443 q ha hb
    | true =>
      simp only [d7809, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7810 q = 1) (hb : d92315 q = 1) : d112114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7810, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85554 q = 1) (hb : d92315 q = 1) : d112115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85554, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85562 q = 1) (hb : d92315 q = 1) : d112125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85562, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85563 q = 1) (hb : d92315 q = 1) : d112126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85563, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d92315 q = 1) : d112127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17446 (p : Pattern) (ha : d7830 p = 1) (hb : d92315 p = 1) : d112134 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1399 q = 1) : d1399 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1405 q = 1) (hb : d92313 q = 1) : d8856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d92313, d8856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1405, d92313, d8856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7829 q = 1) (hb : d92315 q = 1) : d112133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7829, d92315, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7829, d92315, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7830 q = 1) (hb : d92315 q = 1) : d112134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7830, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7830, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17447 (p : Pattern) (ha : d7834 p = 1) (hb : d92315 p = 1) : d98999 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1404 q = 1) : d1404 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1414 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1415 q = 1) (hb : d92313 q = 1) : d7000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1415, d92313, d7000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7833 q = 1) (hb : d92315 q = 1) : d98998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7833, d92315, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7833, d92315, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7834 q = 1) (hb : d92315 q = 1) : d98999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7834, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7834, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17448 (p : Pattern) (ha : d7840 p = 1) (hb : d92315 p = 1) : d112140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7831 q = 1) (hb : d92315 q = 1) : d112135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17446 q ha hb
    | true =>
      simp only [d7831, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7832 q = 1) (hb : d92315 q = 1) : d112136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7832, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7835 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17447 q ha hb
    | true =>
      simp only [d7835, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7836 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7837 q = 1) (hb : d92315 q = 1) : d112137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7837, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7838 q = 1) (hb : d92315 q = 1) : d112138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7838, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7839 q = 1) (hb : d92315 q = 1) : d112139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7839, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7840 q = 1) (hb : d92315 q = 1) : d112140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7840, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17449 (p : Pattern) (ha : d7844 p = 1) (hb : d92315 p = 1) : d112144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17447 q ha hb
    | true =>
      simp only [d7835, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d92315 q = 1) : d1432 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7841 q = 1) (hb : d92315 q = 1) : d112141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7841, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7842 q = 1) (hb : d92315 q = 1) : d112142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7842, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7843 q = 1) (hb : d92315 q = 1) : d112143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7843, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7844 q = 1) (hb : d92315 q = 1) : d112144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7844, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17450 (p : Pattern) (ha : d7859 p = 1) (hb : d92315 p = 1) : d112150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17447 q ha hb
    | true =>
      simp only [d7835, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7856 q = 1) (hb : d92315 q = 1) : d112147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7856, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7856, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7857 q = 1) (hb : d92315 q = 1) : d112148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7857, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7857, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7858 q = 1) (hb : d92315 q = 1) : d112149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7858, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7858, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7859 q = 1) (hb : d92315 q = 1) : d112150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7859, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7859, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17451 (p : Pattern) (ha : d85574 p = 1) (hb : d92315 p = 1) : d112156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7845 q = 1) (hb : d92315 q = 1) : d112145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17448 q ha hb
    | true =>
      simp only [d7845, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17449 q ha hb
  have h2 (q : Pattern) (ha : d85570 q = 1) (hb : d92315 q = 1) : d112146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85570, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7860 q = 1) (hb : d92315 q = 1) : d112151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17450 q ha hb
    | true =>
      simp only [d7860, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7861 q = 1) (hb : d92315 q = 1) : d112152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7861, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d92315 q = 1) : d112153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85571, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d92315 q = 1) : d112154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d92315 q = 1) : d112155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d92315 q = 1) : d112156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17452 (p : Pattern) (ha : d85580 p = 1) (hb : d92315 p = 1) : d112162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d92315 q = 1) : d112056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17430 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d92315 q = 1) : d112057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d92315 q = 1) : d112065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17430 q ha hb
    | true =>
      simp only [d7750, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17432 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d92315 q = 1) : d112066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d92315 q = 1) : d112067 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85558 q = 1) (hb : d92315 q = 1) : d112119 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17439 q ha hb
    | true =>
      simp only [d85558, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17444 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d92315 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7817 q = 1) (hb : d92315 q = 1) : d112121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17433 q ha hb
    | true =>
      simp only [d7817, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85559 q = 1) (hb : d92315 q = 1) : d112122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85559, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85560 q = 1) (hb : d92315 q = 1) : d112123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85560, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85561 q = 1) (hb : d92315 q = 1) : d112124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85561, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85565 q = 1) (hb : d92315 q = 1) : d112128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85565, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17445 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d92315 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85566 q = 1) (hb : d92315 q = 1) : d112129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85566, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85567 q = 1) (hb : d92315 q = 1) : d112130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85567, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85568 q = 1) (hb : d92315 q = 1) : d112131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85568, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85569 q = 1) (hb : d92315 q = 1) : d112132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85569, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85575 q = 1) (hb : d92315 q = 1) : d112157 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85575, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17451 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d92315 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85576 q = 1) (hb : d92315 q = 1) : d112158 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85576, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85577 q = 1) (hb : d92315 q = 1) : d112159 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85577, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85578 q = 1) (hb : d92315 q = 1) : d112160 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85578, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85579 q = 1) (hb : d92315 q = 1) : d112161 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85579, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85580 q = 1) (hb : d92315 q = 1) : d112162 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85580, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro17453 (p : Pattern) (ha : d85586 p = 1) (hb : d92315 p = 1) : d112168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d92315 q = 1) : d112163 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17452 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d92315 q = 1) : d112164 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d92315 q = 1) : d112165 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d92315 q = 1) : d112166 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d92315 q = 1) : d112167 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d92315 q = 1) : d112168 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17454 (p : Pattern) (ha : d7882 p = 1) (hb : d92315 p = 1) : d99028 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1592 q = 1) : d1592 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1606 q = 1) (hb : d92313 q = 1) : d7034 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1606, d92313, d7034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7881 q = 1) (hb : d92315 q = 1) : d99027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7881, d92315, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7881, d92315, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7882 q = 1) (hb : d92315 q = 1) : d99028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7882, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7882, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17455 (p : Pattern) (ha : d7888 p = 1) (hb : d92315 p = 1) : d112175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7885 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7886 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7887 q = 1) (hb : d92315 q = 1) : d112174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7887, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7888 q = 1) (hb : d92315 q = 1) : d112175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17456 (p : Pattern) (ha : d7894 p = 1) (hb : d92315 p = 1) : d112181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92315 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d92315 q = 1) : d112176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17455 q ha hb
    | true =>
      simp only [d7889, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d92315 q = 1) : d112177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d92315 q = 1) : d112178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d92315 q = 1) : d112179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d92315 q = 1) : d112180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7894 q = 1) (hb : d92315 q = 1) : d112181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17457 (p : Pattern) (ha : d7897 p = 1) (hb : d92315 p = 1) : d112184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7885 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7886 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7887 q = 1) (hb : d92315 q = 1) : d112174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7887, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7897 q = 1) (hb : d92315 q = 1) : d112184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7897, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17458 (p : Pattern) (ha : d7903 p = 1) (hb : d92315 p = 1) : d112190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92315 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d92315 q = 1) : d112176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17455 q ha hb
    | true =>
      simp only [d7889, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d92315 q = 1) : d112177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d92315 q = 1) : d112178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d92315 q = 1) : d112179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d92315 q = 1) : d112180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d92315 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7898 q = 1) (hb : d92315 q = 1) : d112185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17457 q ha hb
    | true =>
      simp only [d7898, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7899 q = 1) (hb : d92315 q = 1) : d112186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7900 q = 1) (hb : d92315 q = 1) : d112187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7900, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7901 q = 1) (hb : d92315 q = 1) : d112188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7902 q = 1) (hb : d92315 q = 1) : d112189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7903 q = 1) (hb : d92315 q = 1) : d112190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7903, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro17459 (p : Pattern) (ha : d7970 p = 1) (hb : d92315 p = 1) : d112246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d92315 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d92315 q = 1) : d112176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17455 q ha hb
    | true =>
      simp only [d7889, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d92315 q = 1) : d112177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d92315 q = 1) : d112178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d92315 q = 1) : d112179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d92315 q = 1) : d112180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d92315 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7970 q = 1) (hb : d92315 q = 1) : d112246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7970, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17460 (p : Pattern) (ha : d7908 p = 1) (hb : d92315 p = 1) : d112195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7885 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7886 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7907 q = 1) (hb : d92315 q = 1) : d112194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7908 q = 1) (hb : d92315 q = 1) : d112195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17461 (p : Pattern) (ha : d7915 p = 1) (hb : d92315 p = 1) : d112202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7885 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7913 q = 1) (hb : d92315 q = 1) : d112200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7914 q = 1) (hb : d92315 q = 1) : d112201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7914, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7915 q = 1) (hb : d92315 q = 1) : d112202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17462 (p : Pattern) (ha : d7920 p = 1) (hb : d92315 p = 1) : d112207 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1673 q = 1) : d1673 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1592 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1674 q = 1) (hb : d92313 q = 1) : d8948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d92313, d8948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1674, d92313, d8948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7919 q = 1) (hb : d92315 q = 1) : d112206 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7919, d92315, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7919, d92315, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7920 q = 1) (hb : d92315 q = 1) : d112207 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7920, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7920, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17463 (p : Pattern) (ha : d7926 p = 1) (hb : d92315 p = 1) : d112213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d92315 q = 1) : d112208 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17462 q ha hb
    | true =>
      simp only [d7921, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d92315 q = 1) : d112209 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d92315 q = 1) : d112210 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d92315 q = 1) : d112211 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d92315 q = 1) : d112212 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7926 q = 1) (hb : d92315 q = 1) : d112213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7926, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17464 (p : Pattern) (ha : d7941 p = 1) (hb : d92315 p = 1) : d112219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d92315 q = 1) : d112216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7938, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d92315 q = 1) : d112217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d92315 q = 1) : d112218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7941 q = 1) (hb : d92315 q = 1) : d112219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7941, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7941, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17465 (p : Pattern) (ha : d85594 p = 1) (hb : d92315 p = 1) : d112225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92315 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7909 q = 1) (hb : d92315 q = 1) : d112196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17460 q ha hb
    | true =>
      simp only [d7909, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7910 q = 1) (hb : d92315 q = 1) : d112197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7911 q = 1) (hb : d92315 q = 1) : d112198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7911, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7912 q = 1) (hb : d92315 q = 1) : d112199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92315 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7916 q = 1) (hb : d92315 q = 1) : d112203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17461 q ha hb
    | true =>
      simp only [d7916, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7917 q = 1) (hb : d92315 q = 1) : d112204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7918 q = 1) (hb : d92315 q = 1) : d112205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7918, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7927 q = 1) (hb : d92315 q = 1) : d112214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17463 q ha hb
    | true =>
      simp only [d7927, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17455 q ha hb
  have h11 (q : Pattern) (ha : d85590 q = 1) (hb : d92315 q = 1) : d112215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85590, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7942 q = 1) (hb : d92315 q = 1) : d112220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17464 q ha hb
    | true =>
      simp only [d7942, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7943 q = 1) (hb : d92315 q = 1) : d112221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7943, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85591 q = 1) (hb : d92315 q = 1) : d112222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85591, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85592 q = 1) (hb : d92315 q = 1) : d112223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85592, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85593 q = 1) (hb : d92315 q = 1) : d112224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85593, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85594 q = 1) (hb : d92315 q = 1) : d112225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85594, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17466 (p : Pattern) (ha : d7948 p = 1) (hb : d92315 p = 1) : d112226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7885 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7886 q = 1) (hb : d92315 q = 1) : d112173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7886, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7907 q = 1) (hb : d92315 q = 1) : d112194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7948 q = 1) (hb : d92315 q = 1) : d112226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7948, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17467 (p : Pattern) (ha : d7953 p = 1) (hb : d92315 p = 1) : d112231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7885 q = 1) (hb : d92315 q = 1) : d112172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7913 q = 1) (hb : d92315 q = 1) : d112200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7914 q = 1) (hb : d92315 q = 1) : d112201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7914, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7953 q = 1) (hb : d92315 q = 1) : d112231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7953, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17468 (p : Pattern) (ha : d7957 p = 1) (hb : d92315 p = 1) : d112235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d92315 q = 1) : d112208 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17462 q ha hb
    | true =>
      simp only [d7921, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d92315 q = 1) : d112209 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7923 q = 1) (hb : d92315 q = 1) : d112210 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7923, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7924 q = 1) (hb : d92315 q = 1) : d112211 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7924, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7925 q = 1) (hb : d92315 q = 1) : d112212 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7925, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7957 q = 1) (hb : d92315 q = 1) : d112235 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7957, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17469 (p : Pattern) (ha : d7962 p = 1) (hb : d92315 p = 1) : d112238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17454 q ha hb
    | true =>
      simp only [d7883, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d92315 q = 1) : d112216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7938, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d92315 q = 1) : d112217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d92315 q = 1) : d112218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7962 q = 1) (hb : d92315 q = 1) : d112238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7962, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7962, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17470 (p : Pattern) (ha : d85599 p = 1) (hb : d92315 p = 1) : d112244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d92315 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7909 q = 1) (hb : d92315 q = 1) : d112196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17460 q ha hb
    | true =>
      simp only [d7909, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7910 q = 1) (hb : d92315 q = 1) : d112197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7911 q = 1) (hb : d92315 q = 1) : d112198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7911, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7912 q = 1) (hb : d92315 q = 1) : d112199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d92315 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7916 q = 1) (hb : d92315 q = 1) : d112203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17461 q ha hb
    | true =>
      simp only [d7916, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7917 q = 1) (hb : d92315 q = 1) : d112204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7918 q = 1) (hb : d92315 q = 1) : d112205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7918, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7927 q = 1) (hb : d92315 q = 1) : d112214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17463 q ha hb
    | true =>
      simp only [d7927, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17455 q ha hb
  have h11 (q : Pattern) (ha : d85590 q = 1) (hb : d92315 q = 1) : d112215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85590, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7942 q = 1) (hb : d92315 q = 1) : d112220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17464 q ha hb
    | true =>
      simp only [d7942, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d7943 q = 1) (hb : d92315 q = 1) : d112221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d7943, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85591 q = 1) (hb : d92315 q = 1) : d112222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85591, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85592 q = 1) (hb : d92315 q = 1) : d112223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85592, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85593 q = 1) (hb : d92315 q = 1) : d112224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85593, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1804 q = 1) (hb : d92315 q = 1) : d1804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d7949 q = 1) (hb : d92315 q = 1) : d112227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17466 q ha hb
    | true =>
      simp only [d7949, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7950 q = 1) (hb : d92315 q = 1) : d112228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7951 q = 1) (hb : d92315 q = 1) : d112229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d7951, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d7952 q = 1) (hb : d92315 q = 1) : d112230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1810 q = 1) (hb : d92315 q = 1) : d1810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d7954 q = 1) (hb : d92315 q = 1) : d112232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17467 q ha hb
    | true =>
      simp only [d7954, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7955 q = 1) (hb : d92315 q = 1) : d112233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d7956 q = 1) (hb : d92315 q = 1) : d112234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d7956, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7958 q = 1) (hb : d92315 q = 1) : d112236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17468 q ha hb
    | true =>
      simp only [d7958, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17457 q ha hb
  have h27 (q : Pattern) (ha : d85595 q = 1) (hb : d92315 q = 1) : d112237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85595, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d7963 q = 1) (hb : d92315 q = 1) : d112239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17469 q ha hb
    | true =>
      simp only [d7963, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d7964 q = 1) (hb : d92315 q = 1) : d112240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d7964, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85596 q = 1) (hb : d92315 q = 1) : d112241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85596, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85597 q = 1) (hb : d92315 q = 1) : d112242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85597, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85598 q = 1) (hb : d92315 q = 1) : d112243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85598, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85599 q = 1) (hb : d92315 q = 1) : d112244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85599, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro17471 (p : Pattern) (ha : d85606 p = 1) (hb : d92315 p = 1) : d112253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7958 q = 1) (hb : d92315 q = 1) : d112236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17468 q ha hb
    | true =>
      simp only [d7958, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17457 q ha hb
  have h2 (q : Pattern) (ha : d85595 q = 1) (hb : d92315 q = 1) : d112237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85595, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7963 q = 1) (hb : d92315 q = 1) : d112239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17469 q ha hb
    | true =>
      simp only [d7963, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7964 q = 1) (hb : d92315 q = 1) : d112240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7964, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85596 q = 1) (hb : d92315 q = 1) : d112241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85596, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85604 q = 1) (hb : d92315 q = 1) : d112251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85604, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85605 q = 1) (hb : d92315 q = 1) : d112252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85605, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d92315 q = 1) : d112253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17472 (p : Pattern) (ha : d7984 p = 1) (hb : d92315 p = 1) : d112260 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1876 q = 1) : d1876 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1882 q = 1) (hb : d92313 q = 1) : d9024 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d92313, d9024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1882, d92313, d9024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7983 q = 1) (hb : d92315 q = 1) : d112259 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7983, d92315, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7983, d92315, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7984 q = 1) (hb : d92315 q = 1) : d112260 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7984, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7984, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17473 (p : Pattern) (ha : d7988 p = 1) (hb : d92315 p = 1) : d99061 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1881 q = 1) : d1881 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1891 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1892 q = 1) (hb : d92313 q = 1) : d7080 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1892, d92313, d7080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7987 q = 1) (hb : d92315 q = 1) : d99060 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7987, d92315, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7987, d92315, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7988 q = 1) (hb : d92315 q = 1) : d99061 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7988, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7988, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17474 (p : Pattern) (ha : d7994 p = 1) (hb : d92315 p = 1) : d112266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7985 q = 1) (hb : d92315 q = 1) : d112261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17472 q ha hb
    | true =>
      simp only [d7985, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7986 q = 1) (hb : d92315 q = 1) : d112262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7986, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7989 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17473 q ha hb
    | true =>
      simp only [d7989, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7990 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7991 q = 1) (hb : d92315 q = 1) : d112263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7991, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7992 q = 1) (hb : d92315 q = 1) : d112264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7992, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7993 q = 1) (hb : d92315 q = 1) : d112265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7993, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7994 q = 1) (hb : d92315 q = 1) : d112266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7994, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17475 (p : Pattern) (ha : d7998 p = 1) (hb : d92315 p = 1) : d112270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17473 q ha hb
    | true =>
      simp only [d7989, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d92315 q = 1) : d1909 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7995 q = 1) (hb : d92315 q = 1) : d112267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7995, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7996 q = 1) (hb : d92315 q = 1) : d112268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7996, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7997 q = 1) (hb : d92315 q = 1) : d112269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7997, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7998 q = 1) (hb : d92315 q = 1) : d112270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7998, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17476 (p : Pattern) (ha : d8013 p = 1) (hb : d92315 p = 1) : d112276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17473 q ha hb
    | true =>
      simp only [d7989, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8010 q = 1) (hb : d92315 q = 1) : d112273 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8010, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8010, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8011 q = 1) (hb : d92315 q = 1) : d112274 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8011, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8011, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8012 q = 1) (hb : d92315 q = 1) : d112275 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8012, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8012, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8013 q = 1) (hb : d92315 q = 1) : d112276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8013, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8013, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17477 (p : Pattern) (ha : d85616 p = 1) (hb : d92315 p = 1) : d112282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7999 q = 1) (hb : d92315 q = 1) : d112271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17474 q ha hb
    | true =>
      simp only [d7999, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17475 q ha hb
  have h2 (q : Pattern) (ha : d85612 q = 1) (hb : d92315 q = 1) : d112272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85612, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8014 q = 1) (hb : d92315 q = 1) : d112277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17476 q ha hb
    | true =>
      simp only [d8014, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8015 q = 1) (hb : d92315 q = 1) : d112278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8015, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d92315 q = 1) : d112279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85613, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d92315 q = 1) : d112280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d92315 q = 1) : d112281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d92315 q = 1) : d112282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17478 (p : Pattern) (ha : d85622 p = 1) (hb : d92315 p = 1) : d112288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d92315 q = 1) : d112182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17456 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d92315 q = 1) : d112183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d92315 q = 1) : d112191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17456 q ha hb
    | true =>
      simp only [d7904, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17458 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d92315 q = 1) : d112192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d92315 q = 1) : d112193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85600 q = 1) (hb : d92315 q = 1) : d112245 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17465 q ha hb
    | true =>
      simp only [d85600, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17470 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d92315 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7971 q = 1) (hb : d92315 q = 1) : d112247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17459 q ha hb
    | true =>
      simp only [d7971, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85601 q = 1) (hb : d92315 q = 1) : d112248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85601, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85602 q = 1) (hb : d92315 q = 1) : d112249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85602, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d85603 q = 1) (hb : d92315 q = 1) : d112250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85603, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85607 q = 1) (hb : d92315 q = 1) : d112254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85607, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17471 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d92315 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d85608 q = 1) (hb : d92315 q = 1) : d112255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85608, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85609 q = 1) (hb : d92315 q = 1) : d112256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85609, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85610 q = 1) (hb : d92315 q = 1) : d112257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85610, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d85611 q = 1) (hb : d92315 q = 1) : d112258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85611, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85617 q = 1) (hb : d92315 q = 1) : d112283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85617, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17477 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d92315 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d85618 q = 1) (hb : d92315 q = 1) : d112284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85618, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d85619 q = 1) (hb : d92315 q = 1) : d112285 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85619, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85620 q = 1) (hb : d92315 q = 1) : d112286 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85620, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85621 q = 1) (hb : d92315 q = 1) : d112287 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85621, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d85622 q = 1) (hb : d92315 q = 1) : d112288 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85622, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro17479 (p : Pattern) (ha : d85628 p = 1) (hb : d92315 p = 1) : d112294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d92315 q = 1) : d112289 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17478 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d92315 q = 1) : d112290 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d92315 q = 1) : d112291 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d92315 q = 1) : d112292 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d92315 q = 1) : d112293 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d92315 q = 1) : d112294 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17480 (p : Pattern) (ha : d8037 p = 1) (hb : d92315 p = 1) : d99091 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2075 q = 1) : d2075 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2088 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2089 q = 1) (hb : d92313 q = 1) : d7115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2089, d92313, d7115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8036 q = 1) (hb : d92315 q = 1) : d99090 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8036, d92315, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8036, d92315, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8037 q = 1) (hb : d92315 q = 1) : d99091 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8037, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8037, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17481 (p : Pattern) (ha : d8043 p = 1) (hb : d92315 p = 1) : d112302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8040 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8041 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8042 q = 1) (hb : d92315 q = 1) : d112301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8042, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8043 q = 1) (hb : d92315 q = 1) : d112302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17482 (p : Pattern) (ha : d8049 p = 1) (hb : d92315 p = 1) : d112308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92315 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d92315 q = 1) : d112303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17481 q ha hb
    | true =>
      simp only [d8044, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d92315 q = 1) : d112304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d92315 q = 1) : d112305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d92315 q = 1) : d112306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d92315 q = 1) : d112307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8049 q = 1) (hb : d92315 q = 1) : d112308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17483 (p : Pattern) (ha : d8052 p = 1) (hb : d92315 p = 1) : d112311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8040 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8041 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8042 q = 1) (hb : d92315 q = 1) : d112301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8042, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8052 q = 1) (hb : d92315 q = 1) : d112311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8052, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17484 (p : Pattern) (ha : d8058 p = 1) (hb : d92315 p = 1) : d112317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92315 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d92315 q = 1) : d112303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17481 q ha hb
    | true =>
      simp only [d8044, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d92315 q = 1) : d112304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d92315 q = 1) : d112305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d92315 q = 1) : d112306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d92315 q = 1) : d112307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d92315 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8053 q = 1) (hb : d92315 q = 1) : d112312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17483 q ha hb
    | true =>
      simp only [d8053, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8054 q = 1) (hb : d92315 q = 1) : d112313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8055 q = 1) (hb : d92315 q = 1) : d112314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8055, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8056 q = 1) (hb : d92315 q = 1) : d112315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8057 q = 1) (hb : d92315 q = 1) : d112316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8058 q = 1) (hb : d92315 q = 1) : d112317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8058, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro17485 (p : Pattern) (ha : d8125 p = 1) (hb : d92315 p = 1) : d112373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d92315 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d92315 q = 1) : d112303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17481 q ha hb
    | true =>
      simp only [d8044, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d92315 q = 1) : d112304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d92315 q = 1) : d112305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d92315 q = 1) : d112306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d92315 q = 1) : d112307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d92315 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8125 q = 1) (hb : d92315 q = 1) : d112373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8125, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17486 (p : Pattern) (ha : d8063 p = 1) (hb : d92315 p = 1) : d112322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8040 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8041 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8062 q = 1) (hb : d92315 q = 1) : d112321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8063 q = 1) (hb : d92315 q = 1) : d112322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17487 (p : Pattern) (ha : d8070 p = 1) (hb : d92315 p = 1) : d112329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8040 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8068 q = 1) (hb : d92315 q = 1) : d112327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8069 q = 1) (hb : d92315 q = 1) : d112328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8069, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8070 q = 1) (hb : d92315 q = 1) : d112329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17488 (p : Pattern) (ha : d8075 p = 1) (hb : d92315 p = 1) : d112334 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2152 q = 1) : d2152 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2075 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2153 q = 1) (hb : d92313 q = 1) : d9117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d92313, d9117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2153, d92313, d9117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8074 q = 1) (hb : d92315 q = 1) : d112333 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8074, d92315, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8074, d92315, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8075 q = 1) (hb : d92315 q = 1) : d112334 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8075, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8075, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17489 (p : Pattern) (ha : d8081 p = 1) (hb : d92315 p = 1) : d112340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d92315 q = 1) : d112335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17488 q ha hb
    | true =>
      simp only [d8076, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d92315 q = 1) : d112336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d92315 q = 1) : d112337 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d92315 q = 1) : d112338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d92315 q = 1) : d112339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8081 q = 1) (hb : d92315 q = 1) : d112340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8081, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17490 (p : Pattern) (ha : d8096 p = 1) (hb : d92315 p = 1) : d112346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d92315 q = 1) : d112343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8093, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d92315 q = 1) : d112344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d92315 q = 1) : d112345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8096 q = 1) (hb : d92315 q = 1) : d112346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8096, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8096, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17491 (p : Pattern) (ha : d85637 p = 1) (hb : d92315 p = 1) : d112352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92315 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8064 q = 1) (hb : d92315 q = 1) : d112323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17486 q ha hb
    | true =>
      simp only [d8064, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8065 q = 1) (hb : d92315 q = 1) : d112324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8066 q = 1) (hb : d92315 q = 1) : d112325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8066, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8067 q = 1) (hb : d92315 q = 1) : d112326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92315 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8071 q = 1) (hb : d92315 q = 1) : d112330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17487 q ha hb
    | true =>
      simp only [d8071, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8072 q = 1) (hb : d92315 q = 1) : d112331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8073 q = 1) (hb : d92315 q = 1) : d112332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8073, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8082 q = 1) (hb : d92315 q = 1) : d112341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17489 q ha hb
    | true =>
      simp only [d8082, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17481 q ha hb
  have h11 (q : Pattern) (ha : d85633 q = 1) (hb : d92315 q = 1) : d112342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85633, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8097 q = 1) (hb : d92315 q = 1) : d112347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17490 q ha hb
    | true =>
      simp only [d8097, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8098 q = 1) (hb : d92315 q = 1) : d112348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8098, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85634 q = 1) (hb : d92315 q = 1) : d112349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85634, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85635 q = 1) (hb : d92315 q = 1) : d112350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85635, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85636 q = 1) (hb : d92315 q = 1) : d112351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85636, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85637 q = 1) (hb : d92315 q = 1) : d112352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85637, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro17492 (p : Pattern) (ha : d8103 p = 1) (hb : d92315 p = 1) : d112353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8040 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8041 q = 1) (hb : d92315 q = 1) : d112300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8041, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8062 q = 1) (hb : d92315 q = 1) : d112321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8103 q = 1) (hb : d92315 q = 1) : d112353 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8103, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17493 (p : Pattern) (ha : d8108 p = 1) (hb : d92315 p = 1) : d112358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8040 q = 1) (hb : d92315 q = 1) : d112299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8068 q = 1) (hb : d92315 q = 1) : d112327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8069 q = 1) (hb : d92315 q = 1) : d112328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8069, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8108 q = 1) (hb : d92315 q = 1) : d112358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8108, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro17494 (p : Pattern) (ha : d8112 p = 1) (hb : d92315 p = 1) : d112362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d92315 q = 1) : d112335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17488 q ha hb
    | true =>
      simp only [d8076, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d92315 q = 1) : d112336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d92315 q = 1) : d112337 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d92315 q = 1) : d112338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d92315 q = 1) : d112339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8112 q = 1) (hb : d92315 q = 1) : d112362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8112, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17495 (p : Pattern) (ha : d8117 p = 1) (hb : d92315 p = 1) : d112365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17480 q ha hb
    | true =>
      simp only [d8038, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d92315 q = 1) : d112343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8093, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d92315 q = 1) : d112344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d92315 q = 1) : d112345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8117 q = 1) (hb : d92315 q = 1) : d112365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8117, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8117, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17496 (p : Pattern) (ha : d85642 p = 1) (hb : d92315 p = 1) : d112371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d92315 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8064 q = 1) (hb : d92315 q = 1) : d112323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17486 q ha hb
    | true =>
      simp only [d8064, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8065 q = 1) (hb : d92315 q = 1) : d112324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8066 q = 1) (hb : d92315 q = 1) : d112325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8066, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8067 q = 1) (hb : d92315 q = 1) : d112326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d92315 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8071 q = 1) (hb : d92315 q = 1) : d112330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17487 q ha hb
    | true =>
      simp only [d8071, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8072 q = 1) (hb : d92315 q = 1) : d112331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8073 q = 1) (hb : d92315 q = 1) : d112332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8073, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8082 q = 1) (hb : d92315 q = 1) : d112341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17489 q ha hb
    | true =>
      simp only [d8082, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17481 q ha hb
  have h11 (q : Pattern) (ha : d85633 q = 1) (hb : d92315 q = 1) : d112342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85633, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8097 q = 1) (hb : d92315 q = 1) : d112347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17490 q ha hb
    | true =>
      simp only [d8097, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d8098 q = 1) (hb : d92315 q = 1) : d112348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d8098, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d85634 q = 1) (hb : d92315 q = 1) : d112349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85634, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85635 q = 1) (hb : d92315 q = 1) : d112350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85635, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85636 q = 1) (hb : d92315 q = 1) : d112351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85636, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2282 q = 1) (hb : d92315 q = 1) : d2282 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d8104 q = 1) (hb : d92315 q = 1) : d112354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17492 q ha hb
    | true =>
      simp only [d8104, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8105 q = 1) (hb : d92315 q = 1) : d112355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8106 q = 1) (hb : d92315 q = 1) : d112356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d8106, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d8107 q = 1) (hb : d92315 q = 1) : d112357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d2288 q = 1) (hb : d92315 q = 1) : d2288 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d8109 q = 1) (hb : d92315 q = 1) : d112359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17493 q ha hb
    | true =>
      simp only [d8109, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8110 q = 1) (hb : d92315 q = 1) : d112360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d8111 q = 1) (hb : d92315 q = 1) : d112361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8111, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d8113 q = 1) (hb : d92315 q = 1) : d112363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17494 q ha hb
    | true =>
      simp only [d8113, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17483 q ha hb
  have h27 (q : Pattern) (ha : d85638 q = 1) (hb : d92315 q = 1) : d112364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85638, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d8118 q = 1) (hb : d92315 q = 1) : d112366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17495 q ha hb
    | true =>
      simp only [d8118, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d8119 q = 1) (hb : d92315 q = 1) : d112367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d8119, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d85639 q = 1) (hb : d92315 q = 1) : d112368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d85639, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d85640 q = 1) (hb : d92315 q = 1) : d112369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d85640, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d85641 q = 1) (hb : d92315 q = 1) : d112370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85641, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d85642 q = 1) (hb : d92315 q = 1) : d112371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85642, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro17497 (p : Pattern) (ha : d85649 p = 1) (hb : d92315 p = 1) : d112380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8113 q = 1) (hb : d92315 q = 1) : d112363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17494 q ha hb
    | true =>
      simp only [d8113, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17483 q ha hb
  have h2 (q : Pattern) (ha : d85638 q = 1) (hb : d92315 q = 1) : d112364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85638, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8118 q = 1) (hb : d92315 q = 1) : d112366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17495 q ha hb
    | true =>
      simp only [d8118, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8119 q = 1) (hb : d92315 q = 1) : d112367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8119, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85639 q = 1) (hb : d92315 q = 1) : d112368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85639, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85647 q = 1) (hb : d92315 q = 1) : d112378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85647, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85648 q = 1) (hb : d92315 q = 1) : d112379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85648, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d92315 q = 1) : d112380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17498 (p : Pattern) (ha : d8139 p = 1) (hb : d92315 p = 1) : d112387 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2354 q = 1) : d2354 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2360 q = 1) (hb : d92313 q = 1) : d9193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d92313, d9193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2360, d92313, d9193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8138 q = 1) (hb : d92315 q = 1) : d112386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8138, d92315, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8138, d92315, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8139 q = 1) (hb : d92315 q = 1) : d112387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8139, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8139, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17499 (p : Pattern) (ha : d8143 p = 1) (hb : d92315 p = 1) : d99124 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2359 q = 1) : d2359 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2369 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2370 q = 1) (hb : d92313 q = 1) : d7161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2370, d92313, d7161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8142 q = 1) (hb : d92315 q = 1) : d99123 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8142, d92315, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8142, d92315, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8143 q = 1) (hb : d92315 q = 1) : d99124 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8143, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8143, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
