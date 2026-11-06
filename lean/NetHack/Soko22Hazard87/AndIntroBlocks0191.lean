import NetHack.Soko22Hazard87.AndIntroBlocks0190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro47750 (p : Pattern) (ha : d200249 p = 1) (hb : d201759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200244 q = 1) (hb : d201754 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d200244, d201754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47749 q ha hb
    | true =>
      simp only [d200244, d201754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200245 q = 1) (hb : d201755 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d200245, d201755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200245, d201755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200246 q = 1) (hb : d201756 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d200246, d201756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200246, d201756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200247 q = 1) (hb : d201757 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d200247, d201757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200247, d201757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200248 q = 1) (hb : d201758 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d200248, d201758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200248, d201758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200249 q = 1) (hb : d201759 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d200249, d201759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200249, d201759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47751 (p : Pattern) (ha : d194340 p = 1) (hb : d198467 p = 1) : d201762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47105 q ha hb
    | true =>
      simp only [d20913, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d198467 q = 1) : d200327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20970 q = 1) (hb : d198467 q = 1) : d200328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20971 q = 1) (hb : d198467 q = 1) : d200329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20972 q = 1) (hb : d198467 q = 1) : d200330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194340 q = 1) (hb : d198467 q = 1) : d201762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194340, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47752 (p : Pattern) (ha : d194350 p = 1) (hb : d198467 p = 1) : d201772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d198467 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d198467 q = 1) : d200303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47110 q ha hb
    | true =>
      simp only [d20945, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194346 q = 1) (hb : d198467 q = 1) : d201768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194346, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194347 q = 1) (hb : d198467 q = 1) : d201769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194347, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194348 q = 1) (hb : d198467 q = 1) : d201770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194348, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194349 q = 1) (hb : d198467 q = 1) : d201771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194349, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194350 q = 1) (hb : d198467 q = 1) : d201772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194350, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47753 (p : Pattern) (ha : d194356 p = 1) (hb : d198467 p = 1) : d201778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d198467 q = 1) : d200332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47113 q ha hb
    | true =>
      simp only [d20974, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47114 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d198467 q = 1) : d200333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194338 q = 1) (hb : d198467 q = 1) : d201760 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194338, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194339 q = 1) (hb : d198467 q = 1) : d201761 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194339, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194341 q = 1) (hb : d198467 q = 1) : d201763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194341, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47751 q ha hb
  have h6 (q : Pattern) (ha : d194342 q = 1) (hb : d198467 q = 1) : d201764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194343 q = 1) (hb : d198467 q = 1) : d201765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194344 q = 1) (hb : d198467 q = 1) : d201766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194345 q = 1) (hb : d198467 q = 1) : d201767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194351 q = 1) (hb : d198467 q = 1) : d201773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194351, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47752 q ha hb
  have h11 (q : Pattern) (ha : d194352 q = 1) (hb : d198467 q = 1) : d201774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194353 q = 1) (hb : d198467 q = 1) : d201775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194354 q = 1) (hb : d198467 q = 1) : d201776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194355 q = 1) (hb : d198467 q = 1) : d201777 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194356 q = 1) (hb : d198467 q = 1) : d201778 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47754 (p : Pattern) (ha : d194362 p = 1) (hb : d198467 p = 1) : d201784 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d198467 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d194357 q = 1) (hb : d198467 q = 1) : d201779 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194357, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47753 q ha hb
  have h3 (q : Pattern) (ha : d194358 q = 1) (hb : d198467 q = 1) : d201780 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194358, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194359 q = 1) (hb : d198467 q = 1) : d201781 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194359, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194360 q = 1) (hb : d198467 q = 1) : d201782 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194360, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194361 q = 1) (hb : d198467 q = 1) : d201783 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194361, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194362 q = 1) (hb : d198467 q = 1) : d201784 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194362, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47755 (p : Pattern) (ha : d194365 p = 1) (hb : d198467 p = 1) : d201787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d198467 q = 1) : d200491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47143 q ha hb
    | true =>
      simp only [d21156, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47144 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d198467 q = 1) : d200492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d198467 q = 1) : d200493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d198467 q = 1) : d200494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d198467 q = 1) : d200495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194365 q = 1) (hb : d198467 q = 1) : d201787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194365, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47756 (p : Pattern) (ha : d194376 p = 1) (hb : d198467 p = 1) : d201798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194371 q = 1) (hb : d198467 q = 1) : d201793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47177 q ha hb
    | true =>
      simp only [d194371, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47150 q ha hb
  have h2 (q : Pattern) (ha : d194372 q = 1) (hb : d198467 q = 1) : d201794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194372, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194373 q = 1) (hb : d198467 q = 1) : d201795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194374 q = 1) (hb : d198467 q = 1) : d201796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194374, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194375 q = 1) (hb : d198467 q = 1) : d201797 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194375, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194376 q = 1) (hb : d198467 q = 1) : d201798 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194376, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47757 (p : Pattern) (ha : d194382 p = 1) (hb : d198467 p = 1) : d201804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d198467 q = 1) : d200497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47142 q ha hb
    | true =>
      simp only [d21162, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47145 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d198467 q = 1) : d200498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194363 q = 1) (hb : d198467 q = 1) : d201785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194363, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194364 q = 1) (hb : d198467 q = 1) : d201786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194364, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194366 q = 1) (hb : d198467 q = 1) : d201788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194366, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47755 q ha hb
  have h6 (q : Pattern) (ha : d194367 q = 1) (hb : d198467 q = 1) : d201789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194368 q = 1) (hb : d198467 q = 1) : d201790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194369 q = 1) (hb : d198467 q = 1) : d201791 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194370 q = 1) (hb : d198467 q = 1) : d201792 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194377 q = 1) (hb : d198467 q = 1) : d201799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194377, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47756 q ha hb
  have h11 (q : Pattern) (ha : d194378 q = 1) (hb : d198467 q = 1) : d201800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194379 q = 1) (hb : d198467 q = 1) : d201801 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194380 q = 1) (hb : d198467 q = 1) : d201802 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194381 q = 1) (hb : d198467 q = 1) : d201803 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194382 q = 1) (hb : d198467 q = 1) : d201804 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47758 (p : Pattern) (ha : d194388 p = 1) (hb : d198467 p = 1) : d201810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194383 q = 1) (hb : d198467 q = 1) : d201805 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194383, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47757 q ha hb
  have h2 (q : Pattern) (ha : d194384 q = 1) (hb : d198467 q = 1) : d201806 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194384, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194385 q = 1) (hb : d198467 q = 1) : d201807 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194385, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194386 q = 1) (hb : d198467 q = 1) : d201808 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194386, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194387 q = 1) (hb : d198467 q = 1) : d201809 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194387, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194388 q = 1) (hb : d198467 q = 1) : d201810 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194388, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47759 (p : Pattern) (ha : d194392 p = 1) (hb : d198467 p = 1) : d201814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d198467 q = 1) : d200719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47190 q ha hb
    | true =>
      simp only [d21455, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47191 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d198467 q = 1) : d200720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d198467 q = 1) : d200721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d198467 q = 1) : d200722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d198467 q = 1) : d200723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194392 q = 1) (hb : d198467 q = 1) : d201814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194392, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47760 (p : Pattern) (ha : d194403 p = 1) (hb : d198467 p = 1) : d201825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194398 q = 1) (hb : d198467 q = 1) : d201820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47227 q ha hb
    | true =>
      simp only [d194398, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47199 q ha hb
  have h2 (q : Pattern) (ha : d194399 q = 1) (hb : d198467 q = 1) : d201821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194399, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194400 q = 1) (hb : d198467 q = 1) : d201822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194401 q = 1) (hb : d198467 q = 1) : d201823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194401, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194402 q = 1) (hb : d198467 q = 1) : d201824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194402, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194403 q = 1) (hb : d198467 q = 1) : d201825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194403, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47761 (p : Pattern) (ha : d194409 p = 1) (hb : d198467 p = 1) : d201831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d198467 q = 1) : d200725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47189 q ha hb
    | true =>
      simp only [d21461, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47192 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d198467 q = 1) : d200726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194390 q = 1) (hb : d198467 q = 1) : d201812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194390, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194391 q = 1) (hb : d198467 q = 1) : d201813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194391, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194393 q = 1) (hb : d198467 q = 1) : d201815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194393, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47759 q ha hb
  have h6 (q : Pattern) (ha : d194394 q = 1) (hb : d198467 q = 1) : d201816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194395 q = 1) (hb : d198467 q = 1) : d201817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194396 q = 1) (hb : d198467 q = 1) : d201818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194397 q = 1) (hb : d198467 q = 1) : d201819 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194404 q = 1) (hb : d198467 q = 1) : d201826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194404, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47760 q ha hb
  have h11 (q : Pattern) (ha : d194405 q = 1) (hb : d198467 q = 1) : d201827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194406 q = 1) (hb : d198467 q = 1) : d201828 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194407 q = 1) (hb : d198467 q = 1) : d201829 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194408 q = 1) (hb : d198467 q = 1) : d201830 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194409 q = 1) (hb : d198467 q = 1) : d201831 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47762 (p : Pattern) (ha : d194415 p = 1) (hb : d198467 p = 1) : d201837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194410 q = 1) (hb : d198467 q = 1) : d201832 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194410, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47761 q ha hb
  have h2 (q : Pattern) (ha : d194411 q = 1) (hb : d198467 q = 1) : d201833 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194411, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194412 q = 1) (hb : d198467 q = 1) : d201834 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194412, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194413 q = 1) (hb : d198467 q = 1) : d201835 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194413, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194414 q = 1) (hb : d198467 q = 1) : d201836 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194414, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194415 q = 1) (hb : d198467 q = 1) : d201837 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194415, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47763 (p : Pattern) (ha : d194420 p = 1) (hb : d198467 p = 1) : d201842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d198467 q = 1) : d200977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47247 q ha hb
    | true =>
      simp only [d21808, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47248 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d198467 q = 1) : d200978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d198467 q = 1) : d200979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d198467 q = 1) : d200980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d198467 q = 1) : d200981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194420 q = 1) (hb : d198467 q = 1) : d201842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194420, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47764 (p : Pattern) (ha : d194427 p = 1) (hb : d198467 p = 1) : d201143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d198467 q = 1) : d201129 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47284 q ha hb
    | true =>
      simp only [d22070, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47255 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d198467 q = 1) : d201130 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d198467 q = 1) : d201131 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47255 q ha hb
    | true =>
      simp only [d22079, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47286 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d198467 q = 1) : d201136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22098 q = 1) (hb : d198467 q = 1) : d201133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47255 q ha hb
    | true =>
      simp only [d22098, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47256 q ha hb
  have h9 (q : Pattern) (ha : d22099 q = 1) (hb : d198467 q = 1) : d201134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22100 q = 1) (hb : d198467 q = 1) : d201135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22101 q = 1) (hb : d198467 q = 1) : d201141 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22101, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194426 q = 1) (hb : d198467 q = 1) : d201142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194426, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194427 q = 1) (hb : d198467 q = 1) : d201143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194427, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro47765 (p : Pattern) (ha : d194433 p = 1) (hb : d198467 p = 1) : d201157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194428 q = 1) (hb : d198467 q = 1) : d201144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47764 q ha hb
    | true =>
      simp only [d194428, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194429 q = 1) (hb : d198467 q = 1) : d201145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194429, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d198467 q = 1) : d201152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47257 q ha hb
    | true =>
      simp only [d22104, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d198467 q = 1) : d201153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194430 q = 1) (hb : d198467 q = 1) : d201154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194431 q = 1) (hb : d198467 q = 1) : d201155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194432 q = 1) (hb : d198467 q = 1) : d201156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194433 q = 1) (hb : d198467 q = 1) : d201157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47766 (p : Pattern) (ha : d194439 p = 1) (hb : d198467 p = 1) : d201853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194434 q = 1) (hb : d198467 q = 1) : d201848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47765 q ha hb
    | true =>
      simp only [d194434, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47258 q ha hb
  have h2 (q : Pattern) (ha : d194435 q = 1) (hb : d198467 q = 1) : d201849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194435, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194436 q = 1) (hb : d198467 q = 1) : d201850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194437 q = 1) (hb : d198467 q = 1) : d201851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194437, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194438 q = 1) (hb : d198467 q = 1) : d201852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194438, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194439 q = 1) (hb : d198467 q = 1) : d201853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194439, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47767 (p : Pattern) (ha : d194445 p = 1) (hb : d198467 p = 1) : d201859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d198467 q = 1) : d200983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47246 q ha hb
    | true =>
      simp only [d21814, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47249 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d198467 q = 1) : d200984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194418 q = 1) (hb : d198467 q = 1) : d201840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194418, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194419 q = 1) (hb : d198467 q = 1) : d201841 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194419, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194421 q = 1) (hb : d198467 q = 1) : d201843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194421, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47763 q ha hb
  have h6 (q : Pattern) (ha : d194422 q = 1) (hb : d198467 q = 1) : d201844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194423 q = 1) (hb : d198467 q = 1) : d201845 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194424 q = 1) (hb : d198467 q = 1) : d201846 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194425 q = 1) (hb : d198467 q = 1) : d201847 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194440 q = 1) (hb : d198467 q = 1) : d201854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194440, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47766 q ha hb
  have h11 (q : Pattern) (ha : d194441 q = 1) (hb : d198467 q = 1) : d201855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194442 q = 1) (hb : d198467 q = 1) : d201856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194443 q = 1) (hb : d198467 q = 1) : d201857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194444 q = 1) (hb : d198467 q = 1) : d201858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194445 q = 1) (hb : d198467 q = 1) : d201859 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47768 (p : Pattern) (ha : d194451 p = 1) (hb : d198467 p = 1) : d201865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194446 q = 1) (hb : d198467 q = 1) : d201860 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194446, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47767 q ha hb
  have h2 (q : Pattern) (ha : d194447 q = 1) (hb : d198467 q = 1) : d201861 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194447, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194448 q = 1) (hb : d198467 q = 1) : d201862 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194448, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194449 q = 1) (hb : d198467 q = 1) : d201863 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194449, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194450 q = 1) (hb : d198467 q = 1) : d201864 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194450, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194451 q = 1) (hb : d198467 q = 1) : d201865 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194451, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47769 (p : Pattern) (ha : d194457 p = 1) (hb : d198467 p = 1) : d201871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d198467 q = 1) : d201256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47311 q ha hb
    | true =>
      simp only [d22286, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47312 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d198467 q = 1) : d201257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d198467 q = 1) : d201258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d198467 q = 1) : d201259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d198467 q = 1) : d201260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194457 q = 1) (hb : d198467 q = 1) : d201871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194457, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47770 (p : Pattern) (ha : d194464 p = 1) (hb : d198467 p = 1) : d201407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d198467 q = 1) : d201393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47348 q ha hb
    | true =>
      simp only [d22535, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47319 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d198467 q = 1) : d201394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d198467 q = 1) : d201395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47319 q ha hb
    | true =>
      simp only [d22544, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47350 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d198467 q = 1) : d201400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22563 q = 1) (hb : d198467 q = 1) : d201397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47319 q ha hb
    | true =>
      simp only [d22563, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47320 q ha hb
  have h9 (q : Pattern) (ha : d22564 q = 1) (hb : d198467 q = 1) : d201398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22565 q = 1) (hb : d198467 q = 1) : d201399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22566 q = 1) (hb : d198467 q = 1) : d201405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22566, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194463 q = 1) (hb : d198467 q = 1) : d201406 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194463, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194464 q = 1) (hb : d198467 q = 1) : d201407 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194464, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro47771 (p : Pattern) (ha : d194470 p = 1) (hb : d198467 p = 1) : d201421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194465 q = 1) (hb : d198467 q = 1) : d201408 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47770 q ha hb
    | true =>
      simp only [d194465, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194466 q = 1) (hb : d198467 q = 1) : d201409 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194466, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d198467 q = 1) : d201416 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47321 q ha hb
    | true =>
      simp only [d22569, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d198467 q = 1) : d201417 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194467 q = 1) (hb : d198467 q = 1) : d201418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194468 q = 1) (hb : d198467 q = 1) : d201419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194469 q = 1) (hb : d198467 q = 1) : d201420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194470 q = 1) (hb : d198467 q = 1) : d201421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47772 (p : Pattern) (ha : d194476 p = 1) (hb : d198467 p = 1) : d201882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194471 q = 1) (hb : d198467 q = 1) : d201877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47771 q ha hb
    | true =>
      simp only [d194471, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47322 q ha hb
  have h2 (q : Pattern) (ha : d194472 q = 1) (hb : d198467 q = 1) : d201878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194472, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194473 q = 1) (hb : d198467 q = 1) : d201879 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194474 q = 1) (hb : d198467 q = 1) : d201880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194474, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194475 q = 1) (hb : d198467 q = 1) : d201881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194475, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194476 q = 1) (hb : d198467 q = 1) : d201882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194476, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47773 (p : Pattern) (ha : d194482 p = 1) (hb : d198467 p = 1) : d201888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d198467 q = 1) : d201262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47310 q ha hb
    | true =>
      simp only [d22292, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47313 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d198467 q = 1) : d201263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194455 q = 1) (hb : d198467 q = 1) : d201869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194455, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194456 q = 1) (hb : d198467 q = 1) : d201870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194456, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194458 q = 1) (hb : d198467 q = 1) : d201872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194458, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47769 q ha hb
  have h6 (q : Pattern) (ha : d194459 q = 1) (hb : d198467 q = 1) : d201873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194460 q = 1) (hb : d198467 q = 1) : d201874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194461 q = 1) (hb : d198467 q = 1) : d201875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194462 q = 1) (hb : d198467 q = 1) : d201876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194477 q = 1) (hb : d198467 q = 1) : d201883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194477, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47772 q ha hb
  have h11 (q : Pattern) (ha : d194478 q = 1) (hb : d198467 q = 1) : d201884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194479 q = 1) (hb : d198467 q = 1) : d201885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194480 q = 1) (hb : d198467 q = 1) : d201886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194481 q = 1) (hb : d198467 q = 1) : d201887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194482 q = 1) (hb : d198467 q = 1) : d201888 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47774 (p : Pattern) (ha : d194488 p = 1) (hb : d198467 p = 1) : d201894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194483 q = 1) (hb : d198467 q = 1) : d201889 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194483, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47773 q ha hb
  have h2 (q : Pattern) (ha : d194484 q = 1) (hb : d198467 q = 1) : d201890 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194484, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194485 q = 1) (hb : d198467 q = 1) : d201891 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194485, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194486 q = 1) (hb : d198467 q = 1) : d201892 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194486, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194487 q = 1) (hb : d198467 q = 1) : d201893 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194487, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194488 q = 1) (hb : d198467 q = 1) : d201894 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194488, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47775 (p : Pattern) (ha : d194495 p = 1) (hb : d198467 p = 1) : d201901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d198467 q = 1) : d201514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47374 q ha hb
    | true =>
      simp only [d22741, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47375 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d198467 q = 1) : d201515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d198467 q = 1) : d201516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d198467 q = 1) : d201517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d198467 q = 1) : d201518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194495 q = 1) (hb : d198467 q = 1) : d201901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194495, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47776 (p : Pattern) (ha : d194502 p = 1) (hb : d198467 p = 1) : d201653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d198467 q = 1) : d201638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47408 q ha hb
    | true =>
      simp only [d22949, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47382 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d198467 q = 1) : d201639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d198467 q = 1) : d201640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47382 q ha hb
    | true =>
      simp only [d22958, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47409 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d198467 q = 1) : d201646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22977 q = 1) (hb : d198467 q = 1) : d201643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47382 q ha hb
    | true =>
      simp only [d22977, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47383 q ha hb
  have h9 (q : Pattern) (ha : d22978 q = 1) (hb : d198467 q = 1) : d201644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22979 q = 1) (hb : d198467 q = 1) : d201645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22980 q = 1) (hb : d198467 q = 1) : d201651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22980, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194501 q = 1) (hb : d198467 q = 1) : d201652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194501, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194502 q = 1) (hb : d198467 q = 1) : d201653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194502, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro47777 (p : Pattern) (ha : d194508 p = 1) (hb : d198467 p = 1) : d201667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194503 q = 1) (hb : d198467 q = 1) : d201654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47776 q ha hb
    | true =>
      simp only [d194503, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194504 q = 1) (hb : d198467 q = 1) : d201655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194504, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d198467 q = 1) : d201662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47384 q ha hb
    | true =>
      simp only [d22983, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d198467 q = 1) : d201663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194505 q = 1) (hb : d198467 q = 1) : d201664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194506 q = 1) (hb : d198467 q = 1) : d201665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194507 q = 1) (hb : d198467 q = 1) : d201666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194508 q = 1) (hb : d198467 q = 1) : d201667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47778 (p : Pattern) (ha : d194514 p = 1) (hb : d198467 p = 1) : d201912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194509 q = 1) (hb : d198467 q = 1) : d201907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47777 q ha hb
    | true =>
      simp only [d194509, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47385 q ha hb
  have h2 (q : Pattern) (ha : d194510 q = 1) (hb : d198467 q = 1) : d201908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194510, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194511 q = 1) (hb : d198467 q = 1) : d201909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194512 q = 1) (hb : d198467 q = 1) : d201910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194512, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194513 q = 1) (hb : d198467 q = 1) : d201911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194513, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194514 q = 1) (hb : d198467 q = 1) : d201912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194514, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47779 (p : Pattern) (ha : d194520 p = 1) (hb : d198467 p = 1) : d201918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d198467 q = 1) : d201520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47373 q ha hb
    | true =>
      simp only [d22747, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47376 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d198467 q = 1) : d201521 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194493 q = 1) (hb : d198467 q = 1) : d201899 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194493, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194494 q = 1) (hb : d198467 q = 1) : d201900 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194494, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194496 q = 1) (hb : d198467 q = 1) : d201902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194496, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47775 q ha hb
  have h6 (q : Pattern) (ha : d194497 q = 1) (hb : d198467 q = 1) : d201903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d194498 q = 1) (hb : d198467 q = 1) : d201904 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d194499 q = 1) (hb : d198467 q = 1) : d201905 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d194500 q = 1) (hb : d198467 q = 1) : d201906 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194515 q = 1) (hb : d198467 q = 1) : d201913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194515, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47778 q ha hb
  have h11 (q : Pattern) (ha : d194516 q = 1) (hb : d198467 q = 1) : d201914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d194517 q = 1) (hb : d198467 q = 1) : d201915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d194518 q = 1) (hb : d198467 q = 1) : d201916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d194519 q = 1) (hb : d198467 q = 1) : d201917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d194520 q = 1) (hb : d198467 q = 1) : d201918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47780 (p : Pattern) (ha : d194526 p = 1) (hb : d198467 p = 1) : d201924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194521 q = 1) (hb : d198467 q = 1) : d201919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194521, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47779 q ha hb
  have h2 (q : Pattern) (ha : d194522 q = 1) (hb : d198467 q = 1) : d201920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194522, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d194523 q = 1) (hb : d198467 q = 1) : d201921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194523, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194524 q = 1) (hb : d198467 q = 1) : d201922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194524, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d194525 q = 1) (hb : d198467 q = 1) : d201923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194525, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194526 q = 1) (hb : d198467 q = 1) : d201924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194526, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47781 (p : Pattern) (ha : d194532 p = 1) (hb : d198467 p = 1) : d201930 p = 1 := by
  have h0 (q : Pattern) (ha : d194389 q = 1) (hb : d198467 q = 1) : d201811 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47754 q ha hb
    | true =>
      simp only [d194389, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47758 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d194416 q = 1) (hb : d198467 q = 1) : d201838 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194416, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47762 q ha hb
  have h3 (q : Pattern) (ha : d194417 q = 1) (hb : d198467 q = 1) : d201839 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d194452 q = 1) (hb : d198467 q = 1) : d201866 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194452, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47768 q ha hb
  have h5 (q : Pattern) (ha : d194453 q = 1) (hb : d198467 q = 1) : d201867 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194453, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194454 q = 1) (hb : d198467 q = 1) : d201868 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d194489 q = 1) (hb : d198467 q = 1) : d201895 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194489, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47774 q ha hb
  have h8 (q : Pattern) (ha : d194490 q = 1) (hb : d198467 q = 1) : d201896 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194490, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d194491 q = 1) (hb : d198467 q = 1) : d201897 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194491, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d194492 q = 1) (hb : d198467 q = 1) : d201898 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d194527 q = 1) (hb : d198467 q = 1) : d201925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194527, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47780 q ha hb
  have h12 (q : Pattern) (ha : d194528 q = 1) (hb : d198467 q = 1) : d201926 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194528, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d194529 q = 1) (hb : d198467 q = 1) : d201927 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194529, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d194530 q = 1) (hb : d198467 q = 1) : d201928 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194530, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d194531 q = 1) (hb : d198467 q = 1) : d201929 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d194532 q = 1) (hb : d198467 q = 1) : d201930 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro47782 (p : Pattern) (ha : d194538 p = 1) (hb : d198467 p = 1) : d201936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194533 q = 1) (hb : d198467 q = 1) : d201931 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47781 q ha hb
    | true =>
      simp only [d194533, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194534 q = 1) (hb : d198467 q = 1) : d201932 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194535 q = 1) (hb : d198467 q = 1) : d201933 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194536 q = 1) (hb : d198467 q = 1) : d201934 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194537 q = 1) (hb : d198467 q = 1) : d201935 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194538 q = 1) (hb : d198467 q = 1) : d201936 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47783 (p : Pattern) (ha : d194544 p = 1) (hb : d198467 p = 1) : d201942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194539 q = 1) (hb : d198467 q = 1) : d201937 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47782 q ha hb
    | true =>
      simp only [d194539, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194540 q = 1) (hb : d198467 q = 1) : d201938 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194541 q = 1) (hb : d198467 q = 1) : d201939 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194542 q = 1) (hb : d198467 q = 1) : d201940 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194543 q = 1) (hb : d198467 q = 1) : d201941 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194544 q = 1) (hb : d198467 q = 1) : d201942 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47784 (p : Pattern) (ha : d194550 p = 1) (hb : d198467 p = 1) : d201948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194545 q = 1) (hb : d198467 q = 1) : d201943 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47783 q ha hb
    | true =>
      simp only [d194545, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194546 q = 1) (hb : d198467 q = 1) : d201944 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194547 q = 1) (hb : d198467 q = 1) : d201945 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194548 q = 1) (hb : d198467 q = 1) : d201946 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194549 q = 1) (hb : d198467 q = 1) : d201947 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194550 q = 1) (hb : d198467 q = 1) : d201948 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194550, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47785 (p : Pattern) (ha : d194556 p = 1) (hb : d198467 p = 1) : d201954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194551 q = 1) (hb : d198467 q = 1) : d201949 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47784 q ha hb
    | true =>
      simp only [d194551, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194552 q = 1) (hb : d198467 q = 1) : d201950 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194553 q = 1) (hb : d198467 q = 1) : d201951 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194554 q = 1) (hb : d198467 q = 1) : d201952 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194555 q = 1) (hb : d198467 q = 1) : d201953 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194556 q = 1) (hb : d198467 q = 1) : d201954 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47786 (p : Pattern) (ha : d194562 p = 1) (hb : d198467 p = 1) : d201960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194557 q = 1) (hb : d198467 q = 1) : d201955 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47785 q ha hb
    | true =>
      simp only [d194557, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194558 q = 1) (hb : d198467 q = 1) : d201956 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194559 q = 1) (hb : d198467 q = 1) : d201957 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194560 q = 1) (hb : d198467 q = 1) : d201958 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194561 q = 1) (hb : d198467 q = 1) : d201959 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194562 q = 1) (hb : d198467 q = 1) : d201960 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47787 (p : Pattern) (ha : d194568 p = 1) (hb : d198467 p = 1) : d201966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194563 q = 1) (hb : d198467 q = 1) : d201961 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47786 q ha hb
    | true =>
      simp only [d194563, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194564 q = 1) (hb : d198467 q = 1) : d201962 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194565 q = 1) (hb : d198467 q = 1) : d201963 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194566 q = 1) (hb : d198467 q = 1) : d201964 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194567 q = 1) (hb : d198467 q = 1) : d201965 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194568 q = 1) (hb : d198467 q = 1) : d201966 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47788 (p : Pattern) (ha : d194574 p = 1) (hb : d198467 p = 1) : d201972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194569 q = 1) (hb : d198467 q = 1) : d201967 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47787 q ha hb
    | true =>
      simp only [d194569, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194570 q = 1) (hb : d198467 q = 1) : d201968 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194571 q = 1) (hb : d198467 q = 1) : d201969 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194572 q = 1) (hb : d198467 q = 1) : d201970 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194573 q = 1) (hb : d198467 q = 1) : d201971 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194574 q = 1) (hb : d198467 q = 1) : d201972 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47789 (p : Pattern) (ha : d104 p = 1) (hb : d198494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198489 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d198490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d198490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d198490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d198491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d198491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d198491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d198492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d198492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d198492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d198493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d198493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d198493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d198494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d198494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d198494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47790 (p : Pattern) (ha : d111 p = 1) (hb : d198501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198489 q = 1) : d0 q = 1 := by
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
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d198490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d198490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d198490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d198491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d198491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d198491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d198492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d198492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d198492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d198493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d198493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d198493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d198496 q = 1) : d0 q = 1 := by
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
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d198497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d198497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d198497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d198498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d198498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d198498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d198499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d198499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d198499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d198500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d198500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d198500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d198501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d198501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d198501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47791 (p : Pattern) (ha : d406 p = 1) (hb : d198508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198496 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d198497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d198497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d198497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d198498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d198498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d198498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d198506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d198506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d198506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d198507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d198507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d198507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d198508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d198508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d198508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47792 (p : Pattern) (ha : d462 p = 1) (hb : d198537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198532 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d198533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d198533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d198533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d198534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d198534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d198534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d198535 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d198535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d198535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d198536 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d198536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d198536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d198537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d198537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d198537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47793 (p : Pattern) (ha : d53647 p = 1) (hb : d198543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d198502 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d198502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47789 q ha hb
    | true =>
      simp only [d112, d198502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47790 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d198503 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d198503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d198503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d198504 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d198504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d198504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d198505 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d198505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d198505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d198509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d198509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d198509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47791 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d198510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d198510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d198510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d198511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d198511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d198511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d198512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d198512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d198512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d198513 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d198513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d198513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d198538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d198538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d198538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47792 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d198539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d198539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d198539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d198540 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d198540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d198540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d198541 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d198541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d198541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d198542 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d198542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d198542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d198543 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d198543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d198543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47794 (p : Pattern) (ha : d198617 p = 1) (hb : d200324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198489 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198489, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47431 q ha hb
    | true =>
      simp only [d198489, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d198607 q = 1) (hb : d200320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198607, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198607, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198614 q = 1) (hb : d200321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198614, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198614, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198615 q = 1) (hb : d200322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198615, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198615, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198616 q = 1) (hb : d200323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198616, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198616, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198617 q = 1) (hb : d200324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198617, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198617, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47795 (p : Pattern) (ha : d198636 p = 1) (hb : d200331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198489 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198489, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47431 q ha hb
    | true =>
      simp only [d198489, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d198607 q = 1) (hb : d200320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198607, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198607, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198614 q = 1) (hb : d200321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198614, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198614, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198615 q = 1) (hb : d200322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198615, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198615, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198616 q = 1) (hb : d200323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198616, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198616, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198622 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198626 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198496 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198496, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47433 q ha hb
    | true =>
      simp only [d198496, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d198629 q = 1) (hb : d200327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198629, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198629, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198633 q = 1) (hb : d200328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198633, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198633, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198634 q = 1) (hb : d200329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198634, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198634, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198635 q = 1) (hb : d200330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198635, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198635, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198636 q = 1) (hb : d200331 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198636, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198636, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47796 (p : Pattern) (ha : d198645 p = 1) (hb : d201762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198496 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198496, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47433 q ha hb
    | true =>
      simp only [d198496, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d198629 q = 1) (hb : d200327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198629, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198629, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198633 q = 1) (hb : d200328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198633, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198633, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198643 q = 1) (hb : d200329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198643, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198643, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198644 q = 1) (hb : d200330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198644, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198644, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198645 q = 1) (hb : d201762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198645, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198645, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47797 (p : Pattern) (ha : d198685 p = 1) (hb : d201772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198674 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198532 q = 1) (hb : d200303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198532, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47438 q ha hb
    | true =>
      simp only [d198532, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d198675 q = 1) (hb : d201768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198675, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198675, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198682 q = 1) (hb : d201769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198682, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198682, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198683 q = 1) (hb : d201770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198683, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198683, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198684 q = 1) (hb : d201771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198684, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198684, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198685 q = 1) (hb : d201772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198685, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198685, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47798 (p : Pattern) (ha : d198691 p = 1) (hb : d201778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198637 q = 1) (hb : d200332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198637, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47794 q ha hb
    | true =>
      simp only [d198637, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198640 q = 1) (hb : d200333 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198640, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198640, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198641 q = 1) (hb : d201760 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198641, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198641, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198642 q = 1) (hb : d201761 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198642, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198642, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198646 q = 1) (hb : d201763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198646, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198646, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47796 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198647 q = 1) (hb : d201764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198647, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198647, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198648 q = 1) (hb : d201765 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198648, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198648, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198649 q = 1) (hb : d201766 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198649, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198649, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198650 q = 1) (hb : d201767 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198650, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198650, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198686 q = 1) (hb : d201773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198686, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198686, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47797 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198687 q = 1) (hb : d201774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198687, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198687, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198688 q = 1) (hb : d201775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198688, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198688, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198689 q = 1) (hb : d201776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198689, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198689, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198690 q = 1) (hb : d201777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198690, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198690, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198691 q = 1) (hb : d201778 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198691, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198691, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47799 (p : Pattern) (ha : d198697 p = 1) (hb : d201784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d198544 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47793 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d198545 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d198546 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d198547 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d198548 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198692 q = 1) (hb : d201779 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198692, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198692, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47798 q ha hb
  have h8 (q : Pattern) (ha : d198693 q = 1) (hb : d201780 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198693, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198693, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198694 q = 1) (hb : d201781 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198694, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198694, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198695 q = 1) (hb : d201782 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198695, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198695, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198696 q = 1) (hb : d201783 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198696, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198696, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198697 q = 1) (hb : d201784 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198697, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d198697, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro47800 (p : Pattern) (ha : d198808 p = 1) (hb : d200486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198715 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47468 q ha hb
    | true =>
      simp only [d198715, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47469 q ha hb
  have h5 (q : Pattern) (ha : d198798 q = 1) (hb : d200482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198798, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198805 q = 1) (hb : d200483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198805, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198806 q = 1) (hb : d200484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198806, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198807 q = 1) (hb : d200485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198807, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198808 q = 1) (hb : d200486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198808, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198808, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47801 (p : Pattern) (ha : d198829 p = 1) (hb : d200496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198715 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47468 q ha hb
    | true =>
      simp only [d198715, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47469 q ha hb
  have h4 (q : Pattern) (ha : d198798 q = 1) (hb : d200482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198798, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198805 q = 1) (hb : d200483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198805, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198806 q = 1) (hb : d200484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198806, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198807 q = 1) (hb : d200485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198807, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198814 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198819 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198725 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47471 q ha hb
    | true =>
      simp only [d198725, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47472 q ha hb
  have h13 (q : Pattern) (ha : d198822 q = 1) (hb : d200492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198822, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198826 q = 1) (hb : d200493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198826, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198827 q = 1) (hb : d200494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198827, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198827, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198828 q = 1) (hb : d200495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198828, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198828, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198829 q = 1) (hb : d200496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198829, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198829, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47802 (p : Pattern) (ha : d198849 p = 1) (hb : d201787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198725 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47471 q ha hb
    | true =>
      simp only [d198725, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47472 q ha hb
  have h3 (q : Pattern) (ha : d198822 q = 1) (hb : d200492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198822, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198826 q = 1) (hb : d200493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198826, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198847 q = 1) (hb : d200494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198847, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198847, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198848 q = 1) (hb : d200495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198848, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198848, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198849 q = 1) (hb : d201787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198849, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198849, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47803 (p : Pattern) (ha : d198917 p = 1) (hb : d201798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198906 q = 1) (hb : d201793 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198906, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47504 q ha hb
    | true =>
      simp only [d198906, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47507 q ha hb
  have h3 (q : Pattern) (ha : d198907 q = 1) (hb : d201794 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198907, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198907, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198914 q = 1) (hb : d201795 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198914, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198914, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198915 q = 1) (hb : d201796 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198915, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198915, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198916 q = 1) (hb : d201797 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198916, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198916, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198917 q = 1) (hb : d201798 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198917, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198917, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47804 (p : Pattern) (ha : d198930 p = 1) (hb : d201804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198830 q = 1) (hb : d200497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198830, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47800 q ha hb
    | true =>
      simp only [d198830, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47801 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198844 q = 1) (hb : d200498 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198844, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198844, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198845 q = 1) (hb : d201785 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198845, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198845, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198846 q = 1) (hb : d201786 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198846, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198846, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198850 q = 1) (hb : d201788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198850, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198850, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47802 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d198852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198853 q = 1) (hb : d201789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198853, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198853, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198854 q = 1) (hb : d201790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198854, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198854, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198855 q = 1) (hb : d201791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198855, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198855, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198856 q = 1) (hb : d201792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198856, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198856, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198918 q = 1) (hb : d201799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198918, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198918, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47803 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198925 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198926 q = 1) (hb : d201800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198926, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198926, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198927 q = 1) (hb : d201801 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198927, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198927, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198928 q = 1) (hb : d201802 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198928, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198928, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198929 q = 1) (hb : d201803 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198929, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198929, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198930 q = 1) (hb : d201804 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198930, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198930, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47805 (p : Pattern) (ha : d198936 p = 1) (hb : d201810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198931 q = 1) (hb : d201805 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198931, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198931, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47804 q ha hb
  have h2 (q : Pattern) (ha : d198932 q = 1) (hb : d201806 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198932, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198932, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198933 q = 1) (hb : d201807 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198933, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198933, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198934 q = 1) (hb : d201808 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198934, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198934, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198935 q = 1) (hb : d201809 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198935, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198935, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198936 q = 1) (hb : d201810 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198936, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198936, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47806 (p : Pattern) (ha : d199065 p = 1) (hb : d200714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198973 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47517 q ha hb
    | true =>
      simp only [d198973, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47518 q ha hb
  have h5 (q : Pattern) (ha : d199055 q = 1) (hb : d200710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199055, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199062 q = 1) (hb : d200711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199062, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199063 q = 1) (hb : d200712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199063, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199064 q = 1) (hb : d200713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199064, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199065 q = 1) (hb : d200714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199065, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199065, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47807 (p : Pattern) (ha : d199086 p = 1) (hb : d200724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198973 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47517 q ha hb
    | true =>
      simp only [d198973, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47518 q ha hb
  have h4 (q : Pattern) (ha : d199055 q = 1) (hb : d200710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199055, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199062 q = 1) (hb : d200711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199062, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199063 q = 1) (hb : d200712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199063, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199064 q = 1) (hb : d200713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199064, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199071 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199076 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198983 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47520 q ha hb
    | true =>
      simp only [d198983, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47521 q ha hb
  have h13 (q : Pattern) (ha : d199079 q = 1) (hb : d200720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199079, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199083 q = 1) (hb : d200721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199083, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199084 q = 1) (hb : d200722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199084, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199084, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199085 q = 1) (hb : d200723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199085, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199085, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199086 q = 1) (hb : d200724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199086, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199086, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47808 (p : Pattern) (ha : d199106 p = 1) (hb : d201814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198983 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47520 q ha hb
    | true =>
      simp only [d198983, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47521 q ha hb
  have h3 (q : Pattern) (ha : d199079 q = 1) (hb : d200720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199079, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199083 q = 1) (hb : d200721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199083, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199104 q = 1) (hb : d200722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199104, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199104, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199105 q = 1) (hb : d200723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199105, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199105, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199106 q = 1) (hb : d201814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199106, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199106, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47809 (p : Pattern) (ha : d199191 p = 1) (hb : d201825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199180 q = 1) (hb : d201820 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199180, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47556 q ha hb
    | true =>
      simp only [d199180, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47559 q ha hb
  have h3 (q : Pattern) (ha : d199181 q = 1) (hb : d201821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199181, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199181, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199188 q = 1) (hb : d201822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199188, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199188, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199189 q = 1) (hb : d201823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199189, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199189, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199190 q = 1) (hb : d201824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199190, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199190, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199191 q = 1) (hb : d201825 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199191, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199191, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47810 (p : Pattern) (ha : d199204 p = 1) (hb : d201831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199087 q = 1) (hb : d200725 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199087, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47806 q ha hb
    | true =>
      simp only [d199087, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47807 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199101 q = 1) (hb : d200726 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199101, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199101, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199102 q = 1) (hb : d201812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199102, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199102, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199103 q = 1) (hb : d201813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199103, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199103, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199107 q = 1) (hb : d201815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199107, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199107, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47808 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199109 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199110 q = 1) (hb : d201816 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199110, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199110, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199111 q = 1) (hb : d201817 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199111, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199111, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199112 q = 1) (hb : d201818 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199112, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199112, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199113 q = 1) (hb : d201819 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199113, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199113, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199192 q = 1) (hb : d201826 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199192, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199192, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47809 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199200 q = 1) (hb : d201827 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199200, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199200, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199201 q = 1) (hb : d201828 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199201, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199201, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199202 q = 1) (hb : d201829 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199202, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199202, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199203 q = 1) (hb : d201830 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199203, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199203, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199204 q = 1) (hb : d201831 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199204, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199204, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47811 (p : Pattern) (ha : d199210 p = 1) (hb : d201837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199205 q = 1) (hb : d201832 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199205, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199205, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47810 q ha hb
  have h2 (q : Pattern) (ha : d199206 q = 1) (hb : d201833 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199206, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199206, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199207 q = 1) (hb : d201834 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199207, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199207, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199208 q = 1) (hb : d201835 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199208, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199208, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199209 q = 1) (hb : d201836 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199209, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199209, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199210 q = 1) (hb : d201837 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199210, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199210, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47812 (p : Pattern) (ha : d199376 p = 1) (hb : d200972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199283 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47573 q ha hb
    | true =>
      simp only [d199283, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47574 q ha hb
  have h5 (q : Pattern) (ha : d199357 q = 1) (hb : d200968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199357, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199373 q = 1) (hb : d200969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199373, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199374 q = 1) (hb : d200970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199374, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199375 q = 1) (hb : d200971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199375, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199376 q = 1) (hb : d200972 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199376, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199376, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47813 (p : Pattern) (ha : d199397 p = 1) (hb : d200982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199283 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47573 q ha hb
    | true =>
      simp only [d199283, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47574 q ha hb
  have h4 (q : Pattern) (ha : d199357 q = 1) (hb : d200968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199357, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199373 q = 1) (hb : d200969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199373, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199374 q = 1) (hb : d200970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199374, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199375 q = 1) (hb : d200971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199375, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199293 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47576 q ha hb
    | true =>
      simp only [d199293, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47577 q ha hb
  have h13 (q : Pattern) (ha : d199390 q = 1) (hb : d200978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199390, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199394 q = 1) (hb : d200979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199394, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199395 q = 1) (hb : d200980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199395, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199395, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199396 q = 1) (hb : d200981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199396, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199396, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199397 q = 1) (hb : d200982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199397, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199397, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47814 (p : Pattern) (ha : d199417 p = 1) (hb : d201842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199293 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47576 q ha hb
    | true =>
      simp only [d199293, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47577 q ha hb
  have h3 (q : Pattern) (ha : d199390 q = 1) (hb : d200978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199390, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199394 q = 1) (hb : d200979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199394, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199415 q = 1) (hb : d200980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199415, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199415, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199416 q = 1) (hb : d200981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199416, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199416, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199417 q = 1) (hb : d201842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199417, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199417, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47815 (p : Pattern) (ha : d199528 p = 1) (hb : d201853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199508 q = 1) (hb : d201848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199508, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47614 q ha hb
    | true =>
      simp only [d199508, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47619 q ha hb
  have h3 (q : Pattern) (ha : d199509 q = 1) (hb : d201849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199509, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199509, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199525 q = 1) (hb : d201850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199525, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199525, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199526 q = 1) (hb : d201851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199526, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199526, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199527 q = 1) (hb : d201852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199527, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199527, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199528 q = 1) (hb : d201853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199528, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199528, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47816 (p : Pattern) (ha : d199541 p = 1) (hb : d201859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199301 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199398 q = 1) (hb : d200983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199398, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47812 q ha hb
    | true =>
      simp only [d199398, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47813 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199412 q = 1) (hb : d200984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199412, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199412, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199413 q = 1) (hb : d201840 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199413, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199413, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199414 q = 1) (hb : d201841 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199414, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199414, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199418 q = 1) (hb : d201843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199418, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199418, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47814 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199421 q = 1) (hb : d201844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199421, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199421, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199422 q = 1) (hb : d201845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199422, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199422, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199423 q = 1) (hb : d201846 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199423, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199423, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199424 q = 1) (hb : d201847 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199424, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199424, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199529 q = 1) (hb : d201854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199529, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199529, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47815 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199536 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199537 q = 1) (hb : d201855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199537, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199537, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199538 q = 1) (hb : d201856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199538, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199538, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199539 q = 1) (hb : d201857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199539, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199539, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199540 q = 1) (hb : d201858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199540, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199540, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199541 q = 1) (hb : d201859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199541, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199541, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47817 (p : Pattern) (ha : d199547 p = 1) (hb : d201865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199542 q = 1) (hb : d201860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199542, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199542, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47816 q ha hb
  have h2 (q : Pattern) (ha : d199543 q = 1) (hb : d201861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199543, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199543, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199544 q = 1) (hb : d201862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199544, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199544, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199545 q = 1) (hb : d201863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199545, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199545, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199546 q = 1) (hb : d201864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199546, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199546, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199547 q = 1) (hb : d201865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199547, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199547, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47818 (p : Pattern) (ha : d199712 p = 1) (hb : d201251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199617 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47633 q ha hb
    | true =>
      simp only [d199617, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47634 q ha hb
  have h5 (q : Pattern) (ha : d199683 q = 1) (hb : d201247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199683, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199709 q = 1) (hb : d201248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199709, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199710 q = 1) (hb : d201249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199710, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199711 q = 1) (hb : d201250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199711, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199712 q = 1) (hb : d201251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199712, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199712, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47819 (p : Pattern) (ha : d199733 p = 1) (hb : d201261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199617 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47633 q ha hb
    | true =>
      simp only [d199617, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47634 q ha hb
  have h4 (q : Pattern) (ha : d199683 q = 1) (hb : d201247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199683, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199709 q = 1) (hb : d201248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199709, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199710 q = 1) (hb : d201249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199710, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199711 q = 1) (hb : d201250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199711, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199718 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199627 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47636 q ha hb
    | true =>
      simp only [d199627, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47637 q ha hb
  have h13 (q : Pattern) (ha : d199726 q = 1) (hb : d201257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199726, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199730 q = 1) (hb : d201258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199730, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199731 q = 1) (hb : d201259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199731, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199731, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199732 q = 1) (hb : d201260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199732, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199732, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199733 q = 1) (hb : d201261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199733, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199733, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47820 (p : Pattern) (ha : d199753 p = 1) (hb : d201871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199627 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47636 q ha hb
    | true =>
      simp only [d199627, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47637 q ha hb
  have h3 (q : Pattern) (ha : d199726 q = 1) (hb : d201257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199726, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199730 q = 1) (hb : d201258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199730, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199751 q = 1) (hb : d201259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199751, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199751, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199752 q = 1) (hb : d201260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199752, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199752, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199753 q = 1) (hb : d201871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199753, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199753, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47821 (p : Pattern) (ha : d199866 p = 1) (hb : d201882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199835 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199840 q = 1) (hb : d201877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199840, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47674 q ha hb
    | true =>
      simp only [d199840, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47680 q ha hb
  have h3 (q : Pattern) (ha : d199841 q = 1) (hb : d201878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199841, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199841, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199862 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199863 q = 1) (hb : d201879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199863, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199863, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199864 q = 1) (hb : d201880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199864, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199864, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199865 q = 1) (hb : d201881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199865, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199865, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199866 q = 1) (hb : d201882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199866, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199866, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47822 (p : Pattern) (ha : d199879 p = 1) (hb : d201888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199635 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199734 q = 1) (hb : d201262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199734, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47818 q ha hb
    | true =>
      simp only [d199734, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47819 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199748 q = 1) (hb : d201263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199748, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199748, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199749 q = 1) (hb : d201869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199749, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199749, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199750 q = 1) (hb : d201870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199750, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199750, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199754 q = 1) (hb : d201872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199754, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199754, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47820 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199756 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199757 q = 1) (hb : d201873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199757, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199757, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199758 q = 1) (hb : d201874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199758, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199758, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199759 q = 1) (hb : d201875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199759, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199759, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199760 q = 1) (hb : d201876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199760, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199760, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199867 q = 1) (hb : d201883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199867, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199867, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47821 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199874 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199875 q = 1) (hb : d201884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199875, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199875, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199876 q = 1) (hb : d201885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199876, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199876, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199877 q = 1) (hb : d201886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199877, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199877, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199878 q = 1) (hb : d201887 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199878, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199878, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199879 q = 1) (hb : d201888 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199879, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199879, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47823 (p : Pattern) (ha : d199885 p = 1) (hb : d201894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199880 q = 1) (hb : d201889 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199880, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199880, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47822 q ha hb
  have h2 (q : Pattern) (ha : d199881 q = 1) (hb : d201890 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199881, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199881, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199882 q = 1) (hb : d201891 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199882, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199882, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199883 q = 1) (hb : d201892 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199883, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199883, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199884 q = 1) (hb : d201893 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199884, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199884, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199885 q = 1) (hb : d201894 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199885, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199885, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47824 (p : Pattern) (ha : d200035 p = 1) (hb : d201509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199945 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47692 q ha hb
    | true =>
      simp only [d199945, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47693 q ha hb
  have h5 (q : Pattern) (ha : d200000 q = 1) (hb : d201505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d200000, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200032 q = 1) (hb : d201506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200032, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d200033 q = 1) (hb : d201507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200033, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200034 q = 1) (hb : d201508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200034, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200035 q = 1) (hb : d201509 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200035, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200035, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47825 (p : Pattern) (ha : d200056 p = 1) (hb : d201519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199945 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47692 q ha hb
    | true =>
      simp only [d199945, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47693 q ha hb
  have h4 (q : Pattern) (ha : d200000 q = 1) (hb : d201505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200000, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200032 q = 1) (hb : d201506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200032, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d200033 q = 1) (hb : d201507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200033, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200034 q = 1) (hb : d201508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200034, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d200041 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d200046 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199955 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47695 q ha hb
    | true =>
      simp only [d199955, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47696 q ha hb
  have h13 (q : Pattern) (ha : d200049 q = 1) (hb : d201515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d200049, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200053 q = 1) (hb : d201516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200053, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200054 q = 1) (hb : d201517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200054, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d200054, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200055 q = 1) (hb : d201518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200055, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d200055, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200056 q = 1) (hb : d201519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200056, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200056, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47826 (p : Pattern) (ha : d200076 p = 1) (hb : d201901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199955 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47695 q ha hb
    | true =>
      simp only [d199955, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47696 q ha hb
  have h3 (q : Pattern) (ha : d200049 q = 1) (hb : d201515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200049, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200053 q = 1) (hb : d201516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200053, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200074 q = 1) (hb : d201517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200074, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200074, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200075 q = 1) (hb : d201518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200075, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200075, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200076 q = 1) (hb : d201901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200076, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200076, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47827 (p : Pattern) (ha : d200182 p = 1) (hb : d201912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d200151 q = 1) (hb : d201907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200151, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47733 q ha hb
    | true =>
      simp only [d200151, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47739 q ha hb
  have h3 (q : Pattern) (ha : d200152 q = 1) (hb : d201908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200152, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200152, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200179 q = 1) (hb : d201909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200179, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200179, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200180 q = 1) (hb : d201910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200180, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200180, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200181 q = 1) (hb : d201911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200181, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200181, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200182 q = 1) (hb : d201912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200182, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200182, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47828 (p : Pattern) (ha : d200195 p = 1) (hb : d201918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199963 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200057 q = 1) (hb : d201520 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200057, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47824 q ha hb
    | true =>
      simp only [d200057, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47825 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200071 q = 1) (hb : d201521 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200071, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200071, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200072 q = 1) (hb : d201899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200072, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200072, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200073 q = 1) (hb : d201900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200073, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200073, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200077 q = 1) (hb : d201902 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200077, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200077, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47826 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d200079 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d200080 q = 1) (hb : d201903 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200080, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200080, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d200081 q = 1) (hb : d201904 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200081, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200081, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d200082 q = 1) (hb : d201905 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200082, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200082, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d200083 q = 1) (hb : d201906 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200083, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200083, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200183 q = 1) (hb : d201913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200183, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200183, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47827 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200190 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200191 q = 1) (hb : d201914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200191, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200191, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200192 q = 1) (hb : d201915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200192, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200192, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d200193 q = 1) (hb : d201916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200193, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200193, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d200194 q = 1) (hb : d201917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200194, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d200194, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d200195 q = 1) (hb : d201918 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d200195, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200195, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47829 (p : Pattern) (ha : d200201 p = 1) (hb : d201924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200196 q = 1) (hb : d201919 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d200196, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200196, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47828 q ha hb
  have h2 (q : Pattern) (ha : d200197 q = 1) (hb : d201920 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d200197, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200197, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200198 q = 1) (hb : d201921 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d200198, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200198, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200199 q = 1) (hb : d201922 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d200199, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200199, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200200 q = 1) (hb : d201923 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d200200, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200200, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200201 q = 1) (hb : d201924 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d200201, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200201, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47830 (p : Pattern) (ha : d200207 p = 1) (hb : d201930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d198937 q = 1) (hb : d201811 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d198937, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47799 q ha hb
    | true =>
      simp only [d198937, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47805 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199211 q = 1) (hb : d201838 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199211, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199211, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47811 q ha hb
  have h3 (q : Pattern) (ha : d199212 q = 1) (hb : d201839 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199212, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d199212, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199548 q = 1) (hb : d201866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199548, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199548, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47817 q ha hb
  have h5 (q : Pattern) (ha : d199549 q = 1) (hb : d201867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199549, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199549, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199550 q = 1) (hb : d201868 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199550, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199550, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199886 q = 1) (hb : d201895 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199886, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199886, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47823 q ha hb
  have h8 (q : Pattern) (ha : d199887 q = 1) (hb : d201896 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199887, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199887, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199888 q = 1) (hb : d201897 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199888, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199888, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199889 q = 1) (hb : d201898 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d199889, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199889, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200202 q = 1) (hb : d201925 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d200202, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200202, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47829 q ha hb
  have h12 (q : Pattern) (ha : d200203 q = 1) (hb : d201926 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d200203, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200203, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200204 q = 1) (hb : d201927 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d200204, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200204, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200205 q = 1) (hb : d201928 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d200205, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200205, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200206 q = 1) (hb : d201929 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d200206, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200206, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200207 q = 1) (hb : d201930 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d200207, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200207, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro47831 (p : Pattern) (ha : d200213 p = 1) (hb : d201936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200208 q = 1) (hb : d201931 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d200208, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47830 q ha hb
    | true =>
      simp only [d200208, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200209 q = 1) (hb : d201932 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d200209, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200209, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200210 q = 1) (hb : d201933 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d200210, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200210, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200211 q = 1) (hb : d201934 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d200211, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200211, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200212 q = 1) (hb : d201935 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d200212, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200212, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200213 q = 1) (hb : d201936 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d200213, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200213, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47832 (p : Pattern) (ha : d200219 p = 1) (hb : d201942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200214 q = 1) (hb : d201937 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d200214, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47831 q ha hb
    | true =>
      simp only [d200214, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200215 q = 1) (hb : d201938 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d200215, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200215, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200216 q = 1) (hb : d201939 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d200216, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200216, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200217 q = 1) (hb : d201940 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d200217, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200217, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200218 q = 1) (hb : d201941 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d200218, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200218, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200219 q = 1) (hb : d201942 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d200219, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200219, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47833 (p : Pattern) (ha : d200225 p = 1) (hb : d201948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200220 q = 1) (hb : d201943 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d200220, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47832 q ha hb
    | true =>
      simp only [d200220, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200221 q = 1) (hb : d201944 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d200221, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200221, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200222 q = 1) (hb : d201945 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d200222, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200222, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200223 q = 1) (hb : d201946 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d200223, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200223, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200224 q = 1) (hb : d201947 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d200224, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200224, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200225 q = 1) (hb : d201948 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d200225, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200225, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47834 (p : Pattern) (ha : d200231 p = 1) (hb : d201954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200226 q = 1) (hb : d201949 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d200226, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47833 q ha hb
    | true =>
      simp only [d200226, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200227 q = 1) (hb : d201950 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d200227, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200227, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200228 q = 1) (hb : d201951 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d200228, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200228, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200229 q = 1) (hb : d201952 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d200229, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200229, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200230 q = 1) (hb : d201953 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d200230, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200230, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200231 q = 1) (hb : d201954 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d200231, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200231, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47835 (p : Pattern) (ha : d200237 p = 1) (hb : d201960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200232 q = 1) (hb : d201955 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d200232, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47834 q ha hb
    | true =>
      simp only [d200232, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200233 q = 1) (hb : d201956 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d200233, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200233, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200234 q = 1) (hb : d201957 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d200234, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200234, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200235 q = 1) (hb : d201958 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d200235, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200235, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200236 q = 1) (hb : d201959 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d200236, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200236, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200237 q = 1) (hb : d201960 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d200237, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200237, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47836 (p : Pattern) (ha : d200243 p = 1) (hb : d201966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200238 q = 1) (hb : d201961 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d200238, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47835 q ha hb
    | true =>
      simp only [d200238, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200239 q = 1) (hb : d201962 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d200239, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200239, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200240 q = 1) (hb : d201963 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d200240, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200240, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200241 q = 1) (hb : d201964 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d200241, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200241, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200242 q = 1) (hb : d201965 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d200242, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200242, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200243 q = 1) (hb : d201966 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d200243, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200243, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47837 (p : Pattern) (ha : d200249 p = 1) (hb : d201972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200244 q = 1) (hb : d201967 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d200244, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47836 q ha hb
    | true =>
      simp only [d200244, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200245 q = 1) (hb : d201968 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d200245, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200245, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200246 q = 1) (hb : d201969 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d200246, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200246, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200247 q = 1) (hb : d201970 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d200247, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200247, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200248 q = 1) (hb : d201971 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d200248, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200248, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200249 q = 1) (hb : d201972 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d200249, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200249, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro47838 (p : Pattern) (ha : d104 p = 1) (hb : d201977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d201973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d201974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d201975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d201976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d201977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d201977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d201977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47839 (p : Pattern) (ha : d111 p = 1) (hb : d201982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d201973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d201973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d201974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d201974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d201975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d201975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d201976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d201976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25130 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d201978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d201979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d201980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d201980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d201980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d201981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d201981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d201981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d201982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d201982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d201982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47840 (p : Pattern) (ha : d406 p = 1) (hb : d201989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d201978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d201978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d201979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d201979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d201987 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d201987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d201987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d201988 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d201988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d201988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d201989 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d201989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d201989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47841 (p : Pattern) (ha : d462 p = 1) (hb : d201999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25166 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d201995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d201995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d201995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d201996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d201996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d201996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d201997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d201997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d201997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d201998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d201998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d201998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d201999 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d201999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d201999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47842 (p : Pattern) (ha : d53647 p = 1) (hb : d202005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d201983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d201983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47838 q ha hb
    | true =>
      simp only [d112, d201983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47839 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d201984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d201984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d201984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d201985 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d201985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d201985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d201986 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d201986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d201986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d201990 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d201990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d201990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47840 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d201991 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d201991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d201991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d201992 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d201992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d201992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d201993 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d201993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d201993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d201994 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d201994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d201994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d202000 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d202000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d202000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47841 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d202001 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d202001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d202001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d202002 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d202002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d202002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d202003 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d202003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d202003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d202004 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d202004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d202004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d202005 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d202005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d202005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro47843 (p : Pattern) (ha : d200324 p = 1) (hb : d202015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200320 q = 1) (hb : d202011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200320, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200320, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200321 q = 1) (hb : d202012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200321, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200321, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200322 q = 1) (hb : d202013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200322, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200322, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200323 q = 1) (hb : d202014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200323, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200323, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200324 q = 1) (hb : d202015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200324, d202015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200324, d202015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47844 (p : Pattern) (ha : d200331 p = 1) (hb : d202020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d200320 q = 1) (hb : d202011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200320, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200320, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200321 q = 1) (hb : d202012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200321, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200321, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200322 q = 1) (hb : d202013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200322, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200322, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200323 q = 1) (hb : d202014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200323, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200323, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25282 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d200327 q = 1) (hb : d202016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200327, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200327, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200328 q = 1) (hb : d202017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200328, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200328, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200329 q = 1) (hb : d202018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200329, d202018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200329, d202018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200330 q = 1) (hb : d202019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200330, d202019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200330, d202019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200331 q = 1) (hb : d202020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200331, d202020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200331, d202020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47845 (p : Pattern) (ha : d201762 p = 1) (hb : d202027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200327 q = 1) (hb : d202016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200327, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200327, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200328 q = 1) (hb : d202017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200328, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200328, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200329 q = 1) (hb : d202025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200329, d202025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200329, d202025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200330 q = 1) (hb : d202026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200330, d202026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200330, d202026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201762 q = 1) (hb : d202027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201762, d202027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201762, d202027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47846 (p : Pattern) (ha : d201772 p = 1) (hb : d202037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201768 q = 1) (hb : d202033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201768, d202033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201768, d202033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201769 q = 1) (hb : d202034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201769, d202034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201769, d202034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201770 q = 1) (hb : d202035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201770, d202035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201770, d202035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201771 q = 1) (hb : d202036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201771, d202036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201771, d202036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201772 q = 1) (hb : d202037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201772, d202037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201772, d202037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47847 (p : Pattern) (ha : d201778 p = 1) (hb : d202043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200332 q = 1) (hb : d202021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200332, d202021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47843 q ha hb
    | true =>
      simp only [d200332, d202021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47844 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200333 q = 1) (hb : d202022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200333, d202022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200333, d202022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201760 q = 1) (hb : d202023 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201760, d202023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201760, d202023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201761 q = 1) (hb : d202024 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201761, d202024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201761, d202024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201763 q = 1) (hb : d202028 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201763, d202028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201763, d202028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47845 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d201764 q = 1) (hb : d202029 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201764, d202029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201764, d202029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201765 q = 1) (hb : d202030 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201765, d202030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201765, d202030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201766 q = 1) (hb : d202031 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201766, d202031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201766, d202031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d201767 q = 1) (hb : d202032 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201767, d202032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201767, d202032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201773 q = 1) (hb : d202038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201773, d202038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201773, d202038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47846 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201774 q = 1) (hb : d202039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201774, d202039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201774, d202039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201775 q = 1) (hb : d202040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201775, d202040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201775, d202040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d201776 q = 1) (hb : d202041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201776, d202041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d201776, d202041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d201777 q = 1) (hb : d202042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201777, d202042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d201777, d202042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d201778 q = 1) (hb : d202043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d201778, d202043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201778, d202043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47848 (p : Pattern) (ha : d201784 p = 1) (hb : d202049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d202006 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47842 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d202007 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d202008 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d202009 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d202010 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201779 q = 1) (hb : d202044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d201779, d202044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201779, d202044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47847 q ha hb
  have h8 (q : Pattern) (ha : d201780 q = 1) (hb : d202045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d201780, d202045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201780, d202045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201781 q = 1) (hb : d202046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d201781, d202046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201781, d202046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201782 q = 1) (hb : d202047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d201782, d202047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201782, d202047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d201783 q = 1) (hb : d202048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d201783, d202048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201783, d202048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d201784 q = 1) (hb : d202049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d201784, d202049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201784, d202049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro47849 (p : Pattern) (ha : d200486 p = 1) (hb : d202054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200482 q = 1) (hb : d202050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200482, d202050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200482, d202050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200483 q = 1) (hb : d202051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200483, d202051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200483, d202051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200484 q = 1) (hb : d202052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200484, d202052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200484, d202052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200485 q = 1) (hb : d202053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200485, d202053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200485, d202053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200486 q = 1) (hb : d202054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200486, d202054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200486, d202054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47850 (p : Pattern) (ha : d200496 p = 1) (hb : d202059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d200482 q = 1) (hb : d202050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200482, d202050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200482, d202050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200483 q = 1) (hb : d202051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200483, d202051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200483, d202051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200484 q = 1) (hb : d202052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200484, d202052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200484, d202052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200485 q = 1) (hb : d202053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200485, d202053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200485, d202053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25531 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25536 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d200492 q = 1) (hb : d202055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200492, d202055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200492, d202055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200493 q = 1) (hb : d202056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200493, d202056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200493, d202056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200494 q = 1) (hb : d202057 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200494, d202057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200494, d202057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200495 q = 1) (hb : d202058 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200495, d202058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200495, d202058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200496 q = 1) (hb : d202059 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200496, d202059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200496, d202059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47851 (p : Pattern) (ha : d201787 p = 1) (hb : d202066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200492 q = 1) (hb : d202055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200492, d202055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200492, d202055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200493 q = 1) (hb : d202056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200493, d202056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200493, d202056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200494 q = 1) (hb : d202064 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200494, d202064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200494, d202064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200495 q = 1) (hb : d202065 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200495, d202065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200495, d202065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201787 q = 1) (hb : d202066 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201787, d202066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201787, d202066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47852 (p : Pattern) (ha : d201798 p = 1) (hb : d202076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201794 q = 1) (hb : d202072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201794, d202072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201794, d202072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201795 q = 1) (hb : d202073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201795, d202073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201795, d202073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201796 q = 1) (hb : d202074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201796, d202074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201796, d202074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201797 q = 1) (hb : d202075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201797, d202075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201797, d202075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201798 q = 1) (hb : d202076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201798, d202076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201798, d202076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47853 (p : Pattern) (ha : d201804 p = 1) (hb : d202082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25410 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200497 q = 1) (hb : d202060 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200497, d202060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47849 q ha hb
    | true =>
      simp only [d200497, d202060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47850 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200498 q = 1) (hb : d202061 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200498, d202061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200498, d202061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201785 q = 1) (hb : d202062 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201785, d202062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201785, d202062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201786 q = 1) (hb : d202063 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201786, d202063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201786, d202063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201788 q = 1) (hb : d202067 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201788, d202067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201788, d202067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47851 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25572 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d201789 q = 1) (hb : d202068 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201789, d202068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201789, d202068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201790 q = 1) (hb : d202069 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201790, d202069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201790, d202069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201791 q = 1) (hb : d202070 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201791, d202070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201791, d202070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d201792 q = 1) (hb : d202071 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201792, d202071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201792, d202071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201799 q = 1) (hb : d202077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201799, d202077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201799, d202077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47852 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201800 q = 1) (hb : d202078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201800, d202078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201800, d202078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201801 q = 1) (hb : d202079 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201801, d202079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201801, d202079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d201802 q = 1) (hb : d202080 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201802, d202080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d201802, d202080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d201803 q = 1) (hb : d202081 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201803, d202081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d201803, d202081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d201804 q = 1) (hb : d202082 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d201804, d202082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201804, d202082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47854 (p : Pattern) (ha : d201810 p = 1) (hb : d202088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201805 q = 1) (hb : d202083 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d201805, d202083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201805, d202083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47853 q ha hb
  have h2 (q : Pattern) (ha : d201806 q = 1) (hb : d202084 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d201806, d202084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201806, d202084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201807 q = 1) (hb : d202085 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d201807, d202085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201807, d202085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201808 q = 1) (hb : d202086 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d201808, d202086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201808, d202086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201809 q = 1) (hb : d202087 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d201809, d202087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201809, d202087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201810 q = 1) (hb : d202088 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d201810, d202088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201810, d202088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47855 (p : Pattern) (ha : d200714 p = 1) (hb : d202094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200710 q = 1) (hb : d202090 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200710, d202090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200710, d202090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200711 q = 1) (hb : d202091 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200711, d202091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200711, d202091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200712 q = 1) (hb : d202092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200712, d202092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200712, d202092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200713 q = 1) (hb : d202093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200713, d202093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200713, d202093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200714 q = 1) (hb : d202094 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200714, d202094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200714, d202094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47856 (p : Pattern) (ha : d200724 p = 1) (hb : d202099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d200710 q = 1) (hb : d202090 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200710, d202090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200710, d202090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200711 q = 1) (hb : d202091 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200711, d202091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200711, d202091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200712 q = 1) (hb : d202092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200712, d202092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200712, d202092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200713 q = 1) (hb : d202093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200713, d202093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200713, d202093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25892 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d200720 q = 1) (hb : d202095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200720, d202095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200720, d202095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200721 q = 1) (hb : d202096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200721, d202096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200721, d202096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200722 q = 1) (hb : d202097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200722, d202097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200722, d202097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200723 q = 1) (hb : d202098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200723, d202098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200723, d202098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200724 q = 1) (hb : d202099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200724, d202099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200724, d202099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47857 (p : Pattern) (ha : d201814 p = 1) (hb : d202106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200720 q = 1) (hb : d202095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200720, d202095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200720, d202095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200721 q = 1) (hb : d202096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200721, d202096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200721, d202096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200722 q = 1) (hb : d202104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200722, d202104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200722, d202104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200723 q = 1) (hb : d202105 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200723, d202105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200723, d202105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201814 q = 1) (hb : d202106 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201814, d202106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201814, d202106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47858 (p : Pattern) (ha : d201825 p = 1) (hb : d202116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201821 q = 1) (hb : d202112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201821, d202112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201821, d202112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201822 q = 1) (hb : d202113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201822, d202113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201822, d202113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201823 q = 1) (hb : d202114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201823, d202114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201823, d202114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201824 q = 1) (hb : d202115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201824, d202115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201824, d202115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201825 q = 1) (hb : d202116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201825, d202116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201825, d202116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47859 (p : Pattern) (ha : d201831 p = 1) (hb : d202122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25743 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200725 q = 1) (hb : d202100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200725, d202100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47855 q ha hb
    | true =>
      simp only [d200725, d202100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47856 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200726 q = 1) (hb : d202101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200726, d202101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200726, d202101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201812 q = 1) (hb : d202102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201812, d202102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201812, d202102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201813 q = 1) (hb : d202103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201813, d202103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201813, d202103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201815 q = 1) (hb : d202107 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201815, d202107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201815, d202107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47857 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25928 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d201816 q = 1) (hb : d202108 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201816, d202108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201816, d202108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201817 q = 1) (hb : d202109 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201817, d202109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201817, d202109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201818 q = 1) (hb : d202110 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201818, d202110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201818, d202110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d201819 q = 1) (hb : d202111 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201819, d202111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201819, d202111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201826 q = 1) (hb : d202117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201826, d202117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201826, d202117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47858 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26065 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201827 q = 1) (hb : d202118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201827, d202118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201827, d202118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201828 q = 1) (hb : d202119 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201828, d202119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201828, d202119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d201829 q = 1) (hb : d202120 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201829, d202120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d201829, d202120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d201830 q = 1) (hb : d202121 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201830, d202121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d201830, d202121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d201831 q = 1) (hb : d202122 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d201831, d202122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201831, d202122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47860 (p : Pattern) (ha : d201837 p = 1) (hb : d202128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201832 q = 1) (hb : d202123 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d201832, d202123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201832, d202123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47859 q ha hb
  have h2 (q : Pattern) (ha : d201833 q = 1) (hb : d202124 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d201833, d202124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201833, d202124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201834 q = 1) (hb : d202125 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d201834, d202125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201834, d202125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201835 q = 1) (hb : d202126 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d201835, d202126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201835, d202126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201836 q = 1) (hb : d202127 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d201836, d202127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201836, d202127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201837 q = 1) (hb : d202128 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d201837, d202128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201837, d202128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47861 (p : Pattern) (ha : d200972 p = 1) (hb : d202135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200968 q = 1) (hb : d202131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200968, d202131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200968, d202131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200969 q = 1) (hb : d202132 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200969, d202132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200969, d202132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200970 q = 1) (hb : d202133 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200970, d202133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200970, d202133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200971 q = 1) (hb : d202134 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200971, d202134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200971, d202134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200972 q = 1) (hb : d202135 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200972, d202135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200972, d202135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47862 (p : Pattern) (ha : d200982 p = 1) (hb : d202140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d200968 q = 1) (hb : d202131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200968, d202131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200968, d202131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200969 q = 1) (hb : d202132 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200969, d202132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200969, d202132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200970 q = 1) (hb : d202133 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200970, d202133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200970, d202133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200971 q = 1) (hb : d202134 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200971, d202134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200971, d202134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d200978 q = 1) (hb : d202136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200978, d202136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d200978, d202136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200979 q = 1) (hb : d202137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200979, d202137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200979, d202137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200980 q = 1) (hb : d202138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200980, d202138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200980, d202138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200981 q = 1) (hb : d202139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200981, d202139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200981, d202139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200982 q = 1) (hb : d202140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200982, d202140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200982, d202140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47863 (p : Pattern) (ha : d201842 p = 1) (hb : d202147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200978 q = 1) (hb : d202136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200978, d202136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200978, d202136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200979 q = 1) (hb : d202137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200979, d202137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200979, d202137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200980 q = 1) (hb : d202145 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200980, d202145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200980, d202145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200981 q = 1) (hb : d202146 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200981, d202146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d200981, d202146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201842 q = 1) (hb : d202147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201842, d202147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201842, d202147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47864 (p : Pattern) (ha : d201853 p = 1) (hb : d202157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201849 q = 1) (hb : d202153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201849, d202153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201849, d202153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26519 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201850 q = 1) (hb : d202154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201850, d202154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201850, d202154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201851 q = 1) (hb : d202155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201851, d202155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201851, d202155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201852 q = 1) (hb : d202156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201852, d202156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201852, d202156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201853 q = 1) (hb : d202157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201853, d202157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201853, d202157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47865 (p : Pattern) (ha : d201859 p = 1) (hb : d202163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200983 q = 1) (hb : d202141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200983, d202141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47861 q ha hb
    | true =>
      simp only [d200983, d202141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47862 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200984 q = 1) (hb : d202142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200984, d202142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200984, d202142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201840 q = 1) (hb : d202143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201840, d202143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201840, d202143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201841 q = 1) (hb : d202144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201841, d202144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201841, d202144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201843 q = 1) (hb : d202148 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201843, d202148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201843, d202148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47863 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26368 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d201844 q = 1) (hb : d202149 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201844, d202149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201844, d202149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201845 q = 1) (hb : d202150 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201845, d202150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201845, d202150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201846 q = 1) (hb : d202151 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201846, d202151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201846, d202151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d201847 q = 1) (hb : d202152 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201847, d202152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201847, d202152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201854 q = 1) (hb : d202158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201854, d202158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201854, d202158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47864 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26535 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201855 q = 1) (hb : d202159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201855, d202159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201855, d202159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201856 q = 1) (hb : d202160 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201856, d202160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201856, d202160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d201857 q = 1) (hb : d202161 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201857, d202161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d201857, d202161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d201858 q = 1) (hb : d202162 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201858, d202162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d201858, d202162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d201859 q = 1) (hb : d202163 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d201859, d202163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201859, d202163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47866 (p : Pattern) (ha : d201865 p = 1) (hb : d202169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201860 q = 1) (hb : d202164 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d201860, d202164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201860, d202164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47865 q ha hb
  have h2 (q : Pattern) (ha : d201861 q = 1) (hb : d202165 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d201861, d202165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201861, d202165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201862 q = 1) (hb : d202166 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d201862, d202166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201862, d202166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201863 q = 1) (hb : d202167 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d201863, d202167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201863, d202167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201864 q = 1) (hb : d202168 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d201864, d202168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201864, d202168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201865 q = 1) (hb : d202169 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d201865, d202169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201865, d202169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47867 (p : Pattern) (ha : d201251 p = 1) (hb : d202177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201247 q = 1) (hb : d202173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201247, d202173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201247, d202173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d201248 q = 1) (hb : d202174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201248, d202174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201248, d202174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201249 q = 1) (hb : d202175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201249, d202175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201249, d202175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201250 q = 1) (hb : d202176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201250, d202176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201250, d202176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201251 q = 1) (hb : d202177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201251, d202177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201251, d202177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47868 (p : Pattern) (ha : d201261 p = 1) (hb : d202182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d201247 q = 1) (hb : d202173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201247, d202173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201247, d202173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d201248 q = 1) (hb : d202174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201248, d202174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201248, d202174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201249 q = 1) (hb : d202175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201249, d202175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201249, d202175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201250 q = 1) (hb : d202176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201250, d202176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201250, d202176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26793 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d201257 q = 1) (hb : d202178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201257, d202178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201257, d202178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201258 q = 1) (hb : d202179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201258, d202179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201258, d202179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201259 q = 1) (hb : d202180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201259, d202180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201259, d202180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d201260 q = 1) (hb : d202181 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201260, d202181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201260, d202181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d201261 q = 1) (hb : d202182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201261, d202182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201261, d202182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47869 (p : Pattern) (ha : d201871 p = 1) (hb : d202189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201257 q = 1) (hb : d202178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201257, d202178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201257, d202178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201258 q = 1) (hb : d202179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201258, d202179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201258, d202179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201259 q = 1) (hb : d202187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201259, d202187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201259, d202187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201260 q = 1) (hb : d202188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201260, d202188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201260, d202188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201871 q = 1) (hb : d202189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201871, d202189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201871, d202189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47870 (p : Pattern) (ha : d201882 p = 1) (hb : d202199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201877 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201878 q = 1) (hb : d202195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201878, d202195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201878, d202195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201879 q = 1) (hb : d202196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201879, d202196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201879, d202196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201880 q = 1) (hb : d202197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201880, d202197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201880, d202197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201881 q = 1) (hb : d202198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201881, d202198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201881, d202198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201882 q = 1) (hb : d202199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201882, d202199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201882, d202199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47871 (p : Pattern) (ha : d201888 p = 1) (hb : d202205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26634 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201262 q = 1) (hb : d202183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201262, d202183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47867 q ha hb
    | true =>
      simp only [d201262, d202183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47868 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201263 q = 1) (hb : d202184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201263, d202184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201263, d202184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201869 q = 1) (hb : d202185 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201869, d202185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201869, d202185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201870 q = 1) (hb : d202186 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201870, d202186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201870, d202186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201872 q = 1) (hb : d202190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201872, d202190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201872, d202190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47869 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26829 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d201873 q = 1) (hb : d202191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201873, d202191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201873, d202191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201874 q = 1) (hb : d202192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201874, d202192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201874, d202192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201875 q = 1) (hb : d202193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201875, d202193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201875, d202193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d201876 q = 1) (hb : d202194 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201876, d202194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201876, d202194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201883 q = 1) (hb : d202200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201883, d202200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201883, d202200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47870 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26998 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201884 q = 1) (hb : d202201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201884, d202201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201884, d202201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201885 q = 1) (hb : d202202 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201885, d202202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201885, d202202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d201886 q = 1) (hb : d202203 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201886, d202203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d201886, d202203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d201887 q = 1) (hb : d202204 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201887, d202204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d201887, d202204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d201888 q = 1) (hb : d202205 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d201888, d202205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201888, d202205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47872 (p : Pattern) (ha : d201894 p = 1) (hb : d202211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201889 q = 1) (hb : d202206 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d201889, d202206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201889, d202206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47871 q ha hb
  have h2 (q : Pattern) (ha : d201890 q = 1) (hb : d202207 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d201890, d202207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201890, d202207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201891 q = 1) (hb : d202208 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d201891, d202208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201891, d202208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201892 q = 1) (hb : d202209 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d201892, d202209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201892, d202209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201893 q = 1) (hb : d202210 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d201893, d202210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201893, d202210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201894 q = 1) (hb : d202211 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d201894, d202211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201894, d202211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47873 (p : Pattern) (ha : d201509 p = 1) (hb : d202220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201505 q = 1) (hb : d202216 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201505, d202216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201505, d202216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d201506 q = 1) (hb : d202217 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201506, d202217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201506, d202217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201507 q = 1) (hb : d202218 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201507, d202218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201507, d202218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201508 q = 1) (hb : d202219 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201508, d202219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201508, d202219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201509 q = 1) (hb : d202220 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201509, d202220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201509, d202220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47874 (p : Pattern) (ha : d201519 p = 1) (hb : d202225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d201505 q = 1) (hb : d202216 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201505, d202216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201505, d202216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d201506 q = 1) (hb : d202217 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201506, d202217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201506, d202217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201507 q = 1) (hb : d202218 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201507, d202218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201507, d202218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201508 q = 1) (hb : d202219 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201508, d202219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201508, d202219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27221 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d201515 q = 1) (hb : d202221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201515, d202221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201515, d202221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201516 q = 1) (hb : d202222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201516, d202222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201516, d202222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201517 q = 1) (hb : d202223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201517, d202223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201517, d202223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d201518 q = 1) (hb : d202224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201518, d202224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201518, d202224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d201519 q = 1) (hb : d202225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201519, d202225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201519, d202225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro47875 (p : Pattern) (ha : d201901 p = 1) (hb : d202232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201515 q = 1) (hb : d202221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201515, d202221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201515, d202221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201516 q = 1) (hb : d202222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201516, d202222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201516, d202222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201517 q = 1) (hb : d202230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201517, d202230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201517, d202230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201518 q = 1) (hb : d202231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201518, d202231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201518, d202231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201901 q = 1) (hb : d202232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201901, d202232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201901, d202232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47876 (p : Pattern) (ha : d201912 p = 1) (hb : d202242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201907 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201908 q = 1) (hb : d202238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201908, d202238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201908, d202238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27405 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201909 q = 1) (hb : d202239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201909, d202239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201909, d202239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201910 q = 1) (hb : d202240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201910, d202240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201910, d202240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201911 q = 1) (hb : d202241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201911, d202241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201911, d202241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201912 q = 1) (hb : d202242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201912, d202242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201912, d202242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47877 (p : Pattern) (ha : d201918 p = 1) (hb : d202248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201520 q = 1) (hb : d202226 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201520, d202226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47873 q ha hb
    | true =>
      simp only [d201520, d202226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47874 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201521 q = 1) (hb : d202227 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201521, d202227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201521, d202227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201899 q = 1) (hb : d202228 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201899, d202228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201899, d202228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201900 q = 1) (hb : d202229 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201900, d202229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201900, d202229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201902 q = 1) (hb : d202233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201902, d202233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201902, d202233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47875 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d27262 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d201903 q = 1) (hb : d202234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201903, d202234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201903, d202234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201904 q = 1) (hb : d202235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201904, d202235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201904, d202235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201905 q = 1) (hb : d202236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201905, d202236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201905, d202236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d201906 q = 1) (hb : d202237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201906, d202237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201906, d202237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201913 q = 1) (hb : d202243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201913, d202243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201913, d202243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47876 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27421 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d201914 q = 1) (hb : d202244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201914, d202244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201914, d202244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201915 q = 1) (hb : d202245 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201915, d202245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201915, d202245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d201916 q = 1) (hb : d202246 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201916, d202246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d201916, d202246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d201917 q = 1) (hb : d202247 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201917, d202247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d201917, d202247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d201918 q = 1) (hb : d202248 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d201918, d202248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201918, d202248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47878 (p : Pattern) (ha : d201924 p = 1) (hb : d202254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201919 q = 1) (hb : d202249 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d201919, d202249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201919, d202249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47877 q ha hb
  have h2 (q : Pattern) (ha : d201920 q = 1) (hb : d202250 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d201920, d202250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201920, d202250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201921 q = 1) (hb : d202251 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d201921, d202251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201921, d202251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201922 q = 1) (hb : d202252 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d201922, d202252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201922, d202252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201923 q = 1) (hb : d202253 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d201923, d202253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201923, d202253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201924 q = 1) (hb : d202254 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d201924, d202254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201924, d202254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47879 (p : Pattern) (ha : d201930 p = 1) (hb : d202260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d201811 q = 1) (hb : d202089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d201811, d202089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47848 q ha hb
    | true =>
      simp only [d201811, d202089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47854 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d201838 q = 1) (hb : d202129 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d201838, d202129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201838, d202129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47860 q ha hb
  have h3 (q : Pattern) (ha : d201839 q = 1) (hb : d202130 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d201839, d202130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201839, d202130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d201866 q = 1) (hb : d202170 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d201866, d202170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201866, d202170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47866 q ha hb
  have h5 (q : Pattern) (ha : d201867 q = 1) (hb : d202171 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d201867, d202171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201867, d202171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201868 q = 1) (hb : d202172 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d201868, d202172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201868, d202172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201895 q = 1) (hb : d202212 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d201895, d202212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201895, d202212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47872 q ha hb
  have h8 (q : Pattern) (ha : d201896 q = 1) (hb : d202213 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d201896, d202213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201896, d202213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201897 q = 1) (hb : d202214 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d201897, d202214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201897, d202214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201898 q = 1) (hb : d202215 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d201898, d202215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201898, d202215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d201925 q = 1) (hb : d202255 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d201925, d202255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201925, d202255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47878 q ha hb
  have h12 (q : Pattern) (ha : d201926 q = 1) (hb : d202256 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d201926, d202256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201926, d202256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d201927 q = 1) (hb : d202257 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d201927, d202257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201927, d202257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201928 q = 1) (hb : d202258 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d201928, d202258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201928, d202258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d201929 q = 1) (hb : d202259 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d201929, d202259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201929, d202259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d201930 q = 1) (hb : d202260 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d201930, d202260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d201930, d202260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro47880 (p : Pattern) (ha : d201936 p = 1) (hb : d202266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201931 q = 1) (hb : d202261 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d201931, d202261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47879 q ha hb
    | true =>
      simp only [d201931, d202261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201932 q = 1) (hb : d202262 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d201932, d202262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201932, d202262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201933 q = 1) (hb : d202263 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d201933, d202263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201933, d202263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201934 q = 1) (hb : d202264 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d201934, d202264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201934, d202264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201935 q = 1) (hb : d202265 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d201935, d202265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201935, d202265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201936 q = 1) (hb : d202266 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d201936, d202266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201936, d202266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47881 (p : Pattern) (ha : d201942 p = 1) (hb : d202272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201937 q = 1) (hb : d202267 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d201937, d202267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47880 q ha hb
    | true =>
      simp only [d201937, d202267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201938 q = 1) (hb : d202268 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d201938, d202268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201938, d202268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201939 q = 1) (hb : d202269 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d201939, d202269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201939, d202269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201940 q = 1) (hb : d202270 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d201940, d202270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201940, d202270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201941 q = 1) (hb : d202271 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d201941, d202271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201941, d202271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201942 q = 1) (hb : d202272 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d201942, d202272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201942, d202272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47882 (p : Pattern) (ha : d201948 p = 1) (hb : d202278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201943 q = 1) (hb : d202273 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d201943, d202273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47881 q ha hb
    | true =>
      simp only [d201943, d202273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201944 q = 1) (hb : d202274 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d201944, d202274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201944, d202274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201945 q = 1) (hb : d202275 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d201945, d202275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201945, d202275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201946 q = 1) (hb : d202276 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d201946, d202276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201946, d202276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201947 q = 1) (hb : d202277 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d201947, d202277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201947, d202277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201948 q = 1) (hb : d202278 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d201948, d202278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201948, d202278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47883 (p : Pattern) (ha : d201954 p = 1) (hb : d202284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201949 q = 1) (hb : d202279 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d201949, d202279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47882 q ha hb
    | true =>
      simp only [d201949, d202279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201950 q = 1) (hb : d202280 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d201950, d202280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201950, d202280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201951 q = 1) (hb : d202281 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d201951, d202281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201951, d202281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201952 q = 1) (hb : d202282 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d201952, d202282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201952, d202282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201953 q = 1) (hb : d202283 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d201953, d202283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201953, d202283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201954 q = 1) (hb : d202284 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d201954, d202284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201954, d202284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47884 (p : Pattern) (ha : d201960 p = 1) (hb : d202290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201955 q = 1) (hb : d202285 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d201955, d202285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47883 q ha hb
    | true =>
      simp only [d201955, d202285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201956 q = 1) (hb : d202286 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d201956, d202286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201956, d202286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201957 q = 1) (hb : d202287 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d201957, d202287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201957, d202287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201958 q = 1) (hb : d202288 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d201958, d202288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201958, d202288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201959 q = 1) (hb : d202289 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d201959, d202289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201959, d202289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201960 q = 1) (hb : d202290 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d201960, d202290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201960, d202290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47885 (p : Pattern) (ha : d201966 p = 1) (hb : d202296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201961 q = 1) (hb : d202291 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d201961, d202291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47884 q ha hb
    | true =>
      simp only [d201961, d202291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201962 q = 1) (hb : d202292 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d201962, d202292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201962, d202292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201963 q = 1) (hb : d202293 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d201963, d202293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201963, d202293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201964 q = 1) (hb : d202294 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d201964, d202294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201964, d202294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201965 q = 1) (hb : d202295 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d201965, d202295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201965, d202295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201966 q = 1) (hb : d202296 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d201966, d202296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201966, d202296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47886 (p : Pattern) (ha : d201972 p = 1) (hb : d202302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201967 q = 1) (hb : d202297 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d201967, d202297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47885 q ha hb
    | true =>
      simp only [d201967, d202297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d201968 q = 1) (hb : d202298 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d201968, d202298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201968, d202298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d201969 q = 1) (hb : d202299 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d201969, d202299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201969, d202299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d201970 q = 1) (hb : d202300 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d201970, d202300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201970, d202300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d201971 q = 1) (hb : d202301 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d201971, d202301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201971, d202301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d201972 q = 1) (hb : d202302 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d201972, d202302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201972, d202302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47887 (p : Pattern) (ha : d24 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24, d202307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47888 (p : Pattern) (ha : d30 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47889 (p : Pattern) (ha : d36 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47890 (p : Pattern) (ha : d42 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47891 (p : Pattern) (ha : d48 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47892 (p : Pattern) (ha : d49 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47893 (p : Pattern) (ha : d55 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47894 (p : Pattern) (ha : d60 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47895 (p : Pattern) (ha : d71 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47896 (p : Pattern) (ha : d77 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47897 (p : Pattern) (ha : d83 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47896 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47898 (p : Pattern) (ha : d89 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47897 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47899 (p : Pattern) (ha : d95 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47891 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47893 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47894 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47898 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47900 (p : Pattern) (ha : d104 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47901 (p : Pattern) (ha : d111 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
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
theorem andIntro47902 (p : Pattern) (ha : d213 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47903 (p : Pattern) (ha : d116 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47904 (p : Pattern) (ha : d123 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47905 (p : Pattern) (ha : d750 p = 1) (hb : d202307 p = 1) : d205894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20 q = 1) (hb : d202304 q = 1) : d20 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d202306 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d20 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d21, d202306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136 q = 1) (hb : d202306 q = 1) : d205892 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d202306 q = 1) : d205893 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d750 q = 1) (hb : d202307 q = 1) : d205894 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d202307, d205894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d750, d202307, d205894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro47906 (p : Pattern) (ha : d20893 p = 1) (hb : d202307 p = 1) : d205900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20892 q = 1) (hb : d202307 q = 1) : d205899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20892, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20893 q = 1) (hb : d202307 q = 1) : d205900 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d205900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20893, d205900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47907 (p : Pattern) (ha : d20899 p = 1) (hb : d202307 p = 1) : d205906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20894 q = 1) (hb : d202307 q = 1) : d205901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
    | true =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
  have h2 (q : Pattern) (ha : d20895 q = 1) (hb : d202307 q = 1) : d205902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20896 q = 1) (hb : d202307 q = 1) : d205903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20897 q = 1) (hb : d202307 q = 1) : d205904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20897, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20898 q = 1) (hb : d202307 q = 1) : d205905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d205905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20898, d205905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20899 q = 1) (hb : d202307 q = 1) : d205906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d205906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20899, d205906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47908 (p : Pattern) (ha : d20905 p = 1) (hb : d202307 p = 1) : d205912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20904 q = 1) (hb : d202307 q = 1) : d205911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20904, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20905 q = 1) (hb : d202307 q = 1) : d205912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d205912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d205912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47909 (p : Pattern) (ha : d150001 p = 1) (hb : d202307 p = 1) : d205918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47903 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47904 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20906 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
    | true =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
  have h9 (q : Pattern) (ha : d149997 q = 1) (hb : d202307 q = 1) : d205914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d149997, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d149998 q = 1) (hb : d202307 q = 1) : d205915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d205915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149998, d205915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149999 q = 1) (hb : d202307 q = 1) : d205916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d205916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149999, d205916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150000 q = 1) (hb : d202307 q = 1) : d205917 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d205917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150000, d205917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150001 q = 1) (hb : d202307 q = 1) : d205918 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d205918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150001, d205918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47910 (p : Pattern) (ha : d194 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47911 (p : Pattern) (ha : d199 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47912 (p : Pattern) (ha : d20912 p = 1) (hb : d202307 p = 1) : d205919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20904 q = 1) (hb : d202307 q = 1) : d205911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20904, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20912 q = 1) (hb : d202307 q = 1) : d205919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d205919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20912, d205919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47913 (p : Pattern) (ha : d150006 p = 1) (hb : d202307 p = 1) : d205925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47903 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47904 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20906 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
    | true =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
  have h9 (q : Pattern) (ha : d149997 q = 1) (hb : d202307 q = 1) : d205914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d149997, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d149998 q = 1) (hb : d202307 q = 1) : d205915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d205915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149998, d205915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d149999 q = 1) (hb : d202307 q = 1) : d205916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d205916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149999, d205916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150000 q = 1) (hb : d202307 q = 1) : d205917 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d205917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150000, d205917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47910 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47911 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d20913 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47912 q ha hb
    | true =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
  have h23 (q : Pattern) (ha : d150002 q = 1) (hb : d202307 q = 1) : d205921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150002, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150003 q = 1) (hb : d202307 q = 1) : d205922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d205922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150003, d205922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150004 q = 1) (hb : d202307 q = 1) : d205923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d205923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150004, d205923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150005 q = 1) (hb : d202307 q = 1) : d205924 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d205924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150005, d205924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150006 q = 1) (hb : d202307 q = 1) : d205925 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d205925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150006, d205925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro47914 (p : Pattern) (ha : d150013 p = 1) (hb : d202307 p = 1) : d205930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20913 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47912 q ha hb
    | true =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
  have h2 (q : Pattern) (ha : d150002 q = 1) (hb : d202307 q = 1) : d205921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150002, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150003 q = 1) (hb : d202307 q = 1) : d205922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d205922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150003, d205922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150011 q = 1) (hb : d202307 q = 1) : d205923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d205923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150011, d205923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150012 q = 1) (hb : d202307 q = 1) : d205924 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d205924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150012, d205924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150013 q = 1) (hb : d202307 q = 1) : d205930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d205930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150013, d205930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47915 (p : Pattern) (ha : d20932 p = 1) (hb : d202307 p = 1) : d205941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d20931 q = 1) (hb : d202307 q = 1) : d205940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20931, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20932 q = 1) (hb : d202307 q = 1) : d205941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d205941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20932, d205941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47916 (p : Pattern) (ha : d20938 p = 1) (hb : d202307 p = 1) : d205947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20933 q = 1) (hb : d202307 q = 1) : d205942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
    | true =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
  have h2 (q : Pattern) (ha : d20934 q = 1) (hb : d202307 q = 1) : d205943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20935 q = 1) (hb : d202307 q = 1) : d205944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20936 q = 1) (hb : d202307 q = 1) : d205945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20936, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20937 q = 1) (hb : d202307 q = 1) : d205946 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d205946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20937, d205946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20938 q = 1) (hb : d202307 q = 1) : d205947 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d205947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20938, d205947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47917 (p : Pattern) (ha : d20944 p = 1) (hb : d202307 p = 1) : d205953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d202307 q = 1) : d205948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47916 q ha hb
    | true =>
      simp only [d20939, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d202307 q = 1) : d205949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47896 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20941 q = 1) (hb : d202307 q = 1) : d205950 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d205950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d205950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20942 q = 1) (hb : d202307 q = 1) : d205951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d205951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20942, d205951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20943 q = 1) (hb : d202307 q = 1) : d205952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d205952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20943, d205952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20944 q = 1) (hb : d202307 q = 1) : d205953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d205953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20944, d205953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47918 (p : Pattern) (ha : d150023 p = 1) (hb : d202307 p = 1) : d205959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20945 q = 1) (hb : d202307 q = 1) : d205954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47917 q ha hb
    | true =>
      simp only [d20945, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47897 q ha hb
  have h2 (q : Pattern) (ha : d150019 q = 1) (hb : d202307 q = 1) : d205955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d205955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150019, d205955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47897 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150020 q = 1) (hb : d202307 q = 1) : d205956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d205956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150020, d205956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150021 q = 1) (hb : d202307 q = 1) : d205957 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d205957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150021, d205957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150022 q = 1) (hb : d202307 q = 1) : d205958 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d205958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150022, d205958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150023 q = 1) (hb : d202307 q = 1) : d205959 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d205959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150023, d205959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47919 (p : Pattern) (ha : d150029 p = 1) (hb : d202307 p = 1) : d205965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47900 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47900 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47901 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150007 q = 1) (hb : d202307 q = 1) : d205926 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d205926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47909 q ha hb
    | true =>
      simp only [d150007, d205926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47913 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47902 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150008 q = 1) (hb : d202307 q = 1) : d205927 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d205927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150008, d205927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150009 q = 1) (hb : d202307 q = 1) : d205928 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d205928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150009, d205928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150010 q = 1) (hb : d202307 q = 1) : d205929 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d205929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150010, d205929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150014 q = 1) (hb : d202307 q = 1) : d205931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d205931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150014, d205931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47914 q ha hb
  have h12 (q : Pattern) (ha : d150015 q = 1) (hb : d202307 q = 1) : d205932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d205932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150015, d205932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150016 q = 1) (hb : d202307 q = 1) : d205933 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d205933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150016, d205933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150017 q = 1) (hb : d202307 q = 1) : d205934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d205934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150017, d205934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150018 q = 1) (hb : d202307 q = 1) : d205935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d205935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150018, d205935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150024 q = 1) (hb : d202307 q = 1) : d205960 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d205960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150024, d205960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47918 q ha hb
  have h17 (q : Pattern) (ha : d150025 q = 1) (hb : d202307 q = 1) : d205961 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d205961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150025, d205961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d150026 q = 1) (hb : d202307 q = 1) : d205962 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d205962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150026, d205962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d150027 q = 1) (hb : d202307 q = 1) : d205963 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d205963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150027, d205963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d150028 q = 1) (hb : d202307 q = 1) : d205964 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d205964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150028, d205964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150029 q = 1) (hb : d202307 q = 1) : d205965 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d205965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150029, d205965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro47920 (p : Pattern) (ha : d406 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47921 (p : Pattern) (ha : d462 p = 1) (hb : d202307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47897 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47922 (p : Pattern) (ha : d20966 p = 1) (hb : d202307 p = 1) : d205975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
    | true =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d202307 q = 1) : d205971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d202307 q = 1) : d205972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d202307 q = 1) : d205973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d202307 q = 1) : d205974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20966 q = 1) (hb : d202307 q = 1) : d205975 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47923 (p : Pattern) (ha : d20973 p = 1) (hb : d202307 p = 1) : d205982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
    | true =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d202307 q = 1) : d205971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d202307 q = 1) : d205972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d202307 q = 1) : d205973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d202307 q = 1) : d205974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20913 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47912 q ha hb
    | true =>
      simp only [d20913, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
  have h7 (q : Pattern) (ha : d20969 q = 1) (hb : d202307 q = 1) : d205978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20970 q = 1) (hb : d202307 q = 1) : d205979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20970, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20971 q = 1) (hb : d202307 q = 1) : d205980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20972 q = 1) (hb : d202307 q = 1) : d205981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20973 q = 1) (hb : d202307 q = 1) : d205982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20973, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47924 (p : Pattern) (ha : d21058 p = 1) (hb : d202307 p = 1) : d206043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
    | true =>
      simp only [d20906, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d202307 q = 1) : d205971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d202307 q = 1) : d205972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d202307 q = 1) : d205973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d202307 q = 1) : d205974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47890 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21058 q = 1) (hb : d202307 q = 1) : d206043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d206043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21058, d206043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47925 (p : Pattern) (ha : d20978 p = 1) (hb : d202307 p = 1) : d205987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20977 q = 1) (hb : d202307 q = 1) : d205986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20978 q = 1) (hb : d202307 q = 1) : d205987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d205987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d205987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47926 (p : Pattern) (ha : d20985 p = 1) (hb : d202307 p = 1) : d205994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20983 q = 1) (hb : d202307 q = 1) : d205992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20984 q = 1) (hb : d202307 q = 1) : d205993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20984, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20985 q = 1) (hb : d202307 q = 1) : d205994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d205994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d205994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47927 (p : Pattern) (ha : d5450 p = 1) (hb : d202307 p = 1) : d205894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20 q = 1) (hb : d202304 q = 1) : d20 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d135 q = 1) (hb : d202306 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5448 q = 1) (hb : d202306 q = 1) : d205892 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5448, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5449 q = 1) (hb : d202306 q = 1) : d205893 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5449, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5450 q = 1) (hb : d202307 q = 1) : d205894 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5450, d202307, d205894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5450, d202307, d205894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro47928 (p : Pattern) (ha : d132 p = 1) (hb : d202304 p = 1) : d25432 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d131 q = 1) : d131 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132 q = 1) (hb : d202304 q = 1) : d25432 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d202304, d25432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132, d202304, d25432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro47929 (p : Pattern) (ha : d20989 p = 1) (hb : d202307 p = 1) : d206001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d315 q = 1) (hb : d202306 q = 1) : d205998 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d202306, d205998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315, d202306, d205998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d134 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d202304 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d135 q = 1) (hb : d202306 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d135, d202306, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316 q = 1) (hb : d202306 q = 1) : d205999 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d205999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316, d205999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d317 q = 1) (hb : d202306 q = 1) : d206000 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d206000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d317, d206000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20989 q = 1) (hb : d202307 q = 1) : d206001 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d20989, d202307, d206001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20989, d202307, d206001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro47930 (p : Pattern) (ha : d20996 p = 1) (hb : d202307 p = 1) : d206007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d202307 q = 1) : d206004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d202307 q = 1) : d206005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d202307 q = 1) : d206006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d206006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d206006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
    | true =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5452 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5453 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5454 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5454, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d20995 q = 1) (hb : d202307 q = 1) : d205899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20995, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20996 q = 1) (hb : d202307 q = 1) : d206007 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d206007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20996, d206007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47931 (p : Pattern) (ha : d21002 p = 1) (hb : d202307 p = 1) : d206013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47930 q ha hb
    | true =>
      simp only [d20997, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20894 q = 1) (hb : d202307 q = 1) : d205901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
    | true =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
  have h5 (q : Pattern) (ha : d20895 q = 1) (hb : d202307 q = 1) : d205902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20896 q = 1) (hb : d202307 q = 1) : d205903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21000 q = 1) (hb : d202307 q = 1) : d206011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d206011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d206011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20897 q = 1) (hb : d202307 q = 1) : d205904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20897, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21001 q = 1) (hb : d202307 q = 1) : d206012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d206012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21001, d206012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21002 q = 1) (hb : d202307 q = 1) : d206013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d206013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21002, d206013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro47932 (p : Pattern) (ha : d21008 p = 1) (hb : d202307 p = 1) : d206019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47931 q ha hb
    | true =>
      simp only [d21003, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d202307 q = 1) : d206017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d202307 q = 1) : d206018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d202307 q = 1) : d206019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d206019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d206019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47933 (p : Pattern) (ha : d21029 p = 1) (hb : d202307 p = 1) : d205912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d202307 q = 1) : d205911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d202307 q = 1) : d205912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d205912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d205912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47934 (p : Pattern) (ha : d150039 p = 1) (hb : d202307 p = 1) : d206025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20979 q = 1) (hb : d202307 q = 1) : d205988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d205988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47925 q ha hb
    | true =>
      simp only [d20979, d205988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47903 q ha hb
  have h2 (q : Pattern) (ha : d20980 q = 1) (hb : d202307 q = 1) : d205989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d205989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d205989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20981 q = 1) (hb : d202307 q = 1) : d205990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d205990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20981, d205990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20982 q = 1) (hb : d202307 q = 1) : d205991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d205991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d205991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20986 q = 1) (hb : d202307 q = 1) : d205995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d205995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47926 q ha hb
    | true =>
      simp only [d20986, d205995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47904 q ha hb
  have h6 (q : Pattern) (ha : d20987 q = 1) (hb : d202307 q = 1) : d205996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d205996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d205996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20988 q = 1) (hb : d202307 q = 1) : d205997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d205997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20988, d205997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21009 q = 1) (hb : d202307 q = 1) : d206020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47932 q ha hb
    | true =>
      simp only [d21009, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
  have h9 (q : Pattern) (ha : d150035 q = 1) (hb : d202307 q = 1) : d206021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d206021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150035, d206021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21030 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47933 q ha hb
    | true =>
      simp only [d21030, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21031 q = 1) (hb : d202307 q = 1) : d205914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21031, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150036 q = 1) (hb : d202307 q = 1) : d206022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d206022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150036, d206022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150037 q = 1) (hb : d202307 q = 1) : d206023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d206023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150037, d206023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150038 q = 1) (hb : d202307 q = 1) : d206024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d206024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150038, d206024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150039 q = 1) (hb : d202307 q = 1) : d206025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d206025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d206025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47935 (p : Pattern) (ha : d21036 p = 1) (hb : d202307 p = 1) : d206026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20977 q = 1) (hb : d202307 q = 1) : d205986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21036 q = 1) (hb : d202307 q = 1) : d206026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d206026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21036, d206026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47936 (p : Pattern) (ha : d21041 p = 1) (hb : d202307 p = 1) : d206031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47889 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20983 q = 1) (hb : d202307 q = 1) : d205992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20984 q = 1) (hb : d202307 q = 1) : d205993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20984, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21041 q = 1) (hb : d202307 q = 1) : d206031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d206031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21041, d206031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47937 (p : Pattern) (ha : d21045 p = 1) (hb : d202307 p = 1) : d206035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47931 q ha hb
    | true =>
      simp only [d21003, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d202307 q = 1) : d206017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d202307 q = 1) : d206018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d202307 q = 1) : d206035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d206035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d206035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47938 (p : Pattern) (ha : d21050 p = 1) (hb : d202307 p = 1) : d205919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47907 q ha hb
    | true =>
      simp only [d20900, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d202307 q = 1) : d205911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d202307 q = 1) : d205919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d205919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d205919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47939 (p : Pattern) (ha : d150044 p = 1) (hb : d202307 p = 1) : d206041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20979 q = 1) (hb : d202307 q = 1) : d205988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d205988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47925 q ha hb
    | true =>
      simp only [d20979, d205988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47903 q ha hb
  have h2 (q : Pattern) (ha : d20980 q = 1) (hb : d202307 q = 1) : d205989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d205989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d205989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20981 q = 1) (hb : d202307 q = 1) : d205990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d205990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20981, d205990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20982 q = 1) (hb : d202307 q = 1) : d205991 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d205991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d205991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20986 q = 1) (hb : d202307 q = 1) : d205995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d205995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47926 q ha hb
    | true =>
      simp only [d20986, d205995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47904 q ha hb
  have h6 (q : Pattern) (ha : d20987 q = 1) (hb : d202307 q = 1) : d205996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d205996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d205996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20988 q = 1) (hb : d202307 q = 1) : d205997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d205997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20988, d205997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21009 q = 1) (hb : d202307 q = 1) : d206020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47932 q ha hb
    | true =>
      simp only [d21009, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47908 q ha hb
  have h9 (q : Pattern) (ha : d150035 q = 1) (hb : d202307 q = 1) : d206021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d206021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150035, d206021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21030 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47933 q ha hb
    | true =>
      simp only [d21030, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21031 q = 1) (hb : d202307 q = 1) : d205914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21031, d205914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150036 q = 1) (hb : d202307 q = 1) : d206022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d206022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150036, d206022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150037 q = 1) (hb : d202307 q = 1) : d206023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d206023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150037, d206023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150038 q = 1) (hb : d202307 q = 1) : d206024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d206024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150038, d206024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21037 q = 1) (hb : d202307 q = 1) : d206027 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d206027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47935 q ha hb
    | true =>
      simp only [d21037, d206027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47910 q ha hb
  have h16 (q : Pattern) (ha : d21038 q = 1) (hb : d202307 q = 1) : d206028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d206028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d206028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21039 q = 1) (hb : d202307 q = 1) : d206029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d206029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21039, d206029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21040 q = 1) (hb : d202307 q = 1) : d206030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d206030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d206030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21042 q = 1) (hb : d202307 q = 1) : d206032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d206032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47936 q ha hb
    | true =>
      simp only [d21042, d206032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47911 q ha hb
  have h20 (q : Pattern) (ha : d21043 q = 1) (hb : d202307 q = 1) : d206033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d206033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d206033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21044 q = 1) (hb : d202307 q = 1) : d206034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d206034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21044, d206034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21046 q = 1) (hb : d202307 q = 1) : d206036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47937 q ha hb
    | true =>
      simp only [d21046, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47912 q ha hb
  have h23 (q : Pattern) (ha : d150040 q = 1) (hb : d202307 q = 1) : d206037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d206037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150040, d206037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21051 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47938 q ha hb
    | true =>
      simp only [d21051, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21052 q = 1) (hb : d202307 q = 1) : d205921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21052, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150041 q = 1) (hb : d202307 q = 1) : d206038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d206038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150041, d206038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150042 q = 1) (hb : d202307 q = 1) : d206039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d206039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150042, d206039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150043 q = 1) (hb : d202307 q = 1) : d206040 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d206040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150043, d206040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150044 q = 1) (hb : d202307 q = 1) : d206041 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d206041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150044, d206041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro47940 (p : Pattern) (ha : d150051 p = 1) (hb : d202307 p = 1) : d206050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d202307 q = 1) : d206036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47937 q ha hb
    | true =>
      simp only [d21046, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47912 q ha hb
  have h2 (q : Pattern) (ha : d150040 q = 1) (hb : d202307 q = 1) : d206037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d206037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150040, d206037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47938 q ha hb
    | true =>
      simp only [d21051, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d202307 q = 1) : d205921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d205921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d202307 q = 1) : d206038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d206038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d206038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d202307 q = 1) : d206048 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d206048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d206048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d202307 q = 1) : d206049 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d206049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d206049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d202307 q = 1) : d206050 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d206050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d206050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47941 (p : Pattern) (ha : d21077 p = 1) (hb : d202307 p = 1) : d206061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d202307 q = 1) : d206056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d202307 q = 1) : d206057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d202307 q = 1) : d206058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d202307 q = 1) : d206059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21075 q = 1) (hb : d202307 q = 1) : d206060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d206060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21075, d206060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5495 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
  have h15 (q : Pattern) (ha : d5451 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
    | true =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5496 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5496, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5452 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5497 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5497, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5498 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5498, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21076 q = 1) (hb : d202307 q = 1) : d205940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21076, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21077 q = 1) (hb : d202307 q = 1) : d206061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d206061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21077, d206061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro47942 (p : Pattern) (ha : d21083 p = 1) (hb : d202307 p = 1) : d206067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47941 q ha hb
    | true =>
      simp only [d21078, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20933 q = 1) (hb : d202307 q = 1) : d205942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
    | true =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
  have h5 (q : Pattern) (ha : d20934 q = 1) (hb : d202307 q = 1) : d205943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20935 q = 1) (hb : d202307 q = 1) : d205944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21081 q = 1) (hb : d202307 q = 1) : d206065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d206065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d206065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20936 q = 1) (hb : d202307 q = 1) : d205945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20936, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21082 q = 1) (hb : d202307 q = 1) : d206066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d206066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21082, d206066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21083 q = 1) (hb : d202307 q = 1) : d206067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d206067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21083, d206067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro47943 (p : Pattern) (ha : d21089 p = 1) (hb : d202307 p = 1) : d206073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d202307 q = 1) : d206068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47942 q ha hb
    | true =>
      simp only [d21084, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d202307 q = 1) : d206069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d202307 q = 1) : d205948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47916 q ha hb
    | true =>
      simp only [d20939, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d202307 q = 1) : d205949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d202307 q = 1) : d206070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d206070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d206070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d202307 q = 1) : d206071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d206071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d206071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d202307 q = 1) : d206072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d206072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d206072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d202307 q = 1) : d206073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d206073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d206073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47944 (p : Pattern) (ha : d21110 p = 1) (hb : d202307 p = 1) : d205953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d202307 q = 1) : d205948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47916 q ha hb
    | true =>
      simp only [d20939, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d202307 q = 1) : d205949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d202307 q = 1) : d205950 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d205950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d205950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d202307 q = 1) : d205951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d205951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d205951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d202307 q = 1) : d205952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d205952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d205952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d202307 q = 1) : d205953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d205953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d205953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47945 (p : Pattern) (ha : d150061 p = 1) (hb : d202307 p = 1) : d206079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21090 q = 1) (hb : d202307 q = 1) : d206074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21090, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47943 q ha hb
    | true =>
      simp only [d21090, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47917 q ha hb
  have h2 (q : Pattern) (ha : d150057 q = 1) (hb : d202307 q = 1) : d206075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d206075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150057, d206075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21111 q = 1) (hb : d202307 q = 1) : d205954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21111, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47944 q ha hb
    | true =>
      simp only [d21111, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21112 q = 1) (hb : d202307 q = 1) : d205955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21112, d205955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21112, d205955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150058 q = 1) (hb : d202307 q = 1) : d206076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d206076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150058, d206076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150059 q = 1) (hb : d202307 q = 1) : d206077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d206077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150059, d206077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150060 q = 1) (hb : d202307 q = 1) : d206078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d206078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150060, d206078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150061 q = 1) (hb : d202307 q = 1) : d206079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d206079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150061, d206079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47946 (p : Pattern) (ha : d150067 p = 1) (hb : d202307 p = 1) : d206085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20967 q = 1) (hb : d202307 q = 1) : d205976 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20967, d205976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20967, d205976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47922 q ha hb
  have h2 (q : Pattern) (ha : d20968 q = 1) (hb : d202307 q = 1) : d205977 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20968, d205977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20968, d205977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20974 q = 1) (hb : d202307 q = 1) : d205983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47922 q ha hb
    | true =>
      simp only [d20974, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47923 q ha hb
  have h4 (q : Pattern) (ha : d20975 q = 1) (hb : d202307 q = 1) : d205984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20975, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20976 q = 1) (hb : d202307 q = 1) : d205985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20976, d205985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20976, d205985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150045 q = 1) (hb : d202307 q = 1) : d206042 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d206042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47934 q ha hb
    | true =>
      simp only [d150045, d206042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47939 q ha hb
  have h7 (q : Pattern) (ha : d21059 q = 1) (hb : d202307 q = 1) : d206044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21059, d206044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47924 q ha hb
    | true =>
      simp only [d21059, d206044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47901 q ha hb
  have h8 (q : Pattern) (ha : d150046 q = 1) (hb : d202307 q = 1) : d206045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d206045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150046, d206045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150047 q = 1) (hb : d202307 q = 1) : d206046 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d206046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150047, d206046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150048 q = 1) (hb : d202307 q = 1) : d206047 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d206047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150048, d206047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150052 q = 1) (hb : d202307 q = 1) : d206051 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d206051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150052, d206051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47940 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47920 q ha hb
  have h13 (q : Pattern) (ha : d150053 q = 1) (hb : d202307 q = 1) : d206052 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d206052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150053, d206052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150054 q = 1) (hb : d202307 q = 1) : d206053 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d206053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150054, d206053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150055 q = 1) (hb : d202307 q = 1) : d206054 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d206054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150055, d206054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150056 q = 1) (hb : d202307 q = 1) : d206055 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d206055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150056, d206055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150062 q = 1) (hb : d202307 q = 1) : d206080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d206080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150062, d206080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47945 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47921 q ha hb
  have h19 (q : Pattern) (ha : d150063 q = 1) (hb : d202307 q = 1) : d206081 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d206081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150063, d206081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150064 q = 1) (hb : d202307 q = 1) : d206082 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d206082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150064, d206082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150065 q = 1) (hb : d202307 q = 1) : d206083 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d206083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150065, d206083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150066 q = 1) (hb : d202307 q = 1) : d206084 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d206084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150066, d206084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150067 q = 1) (hb : d202307 q = 1) : d206085 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d206085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150067, d206085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro47947 (p : Pattern) (ha : d150073 p = 1) (hb : d202307 p = 1) : d206091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47899 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150030 q = 1) (hb : d202307 q = 1) : d205966 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150030, d205966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150030, d205966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47919 q ha hb
  have h6 (q : Pattern) (ha : d150031 q = 1) (hb : d202307 q = 1) : d205967 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150031, d205967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150031, d205967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150032 q = 1) (hb : d202307 q = 1) : d205968 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150032, d205968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150032, d205968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150033 q = 1) (hb : d202307 q = 1) : d205969 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150033, d205969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150033, d205969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150034 q = 1) (hb : d202307 q = 1) : d205970 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150034, d205970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150034, d205970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150068 q = 1) (hb : d202307 q = 1) : d206086 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d206086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150068, d206086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47946 q ha hb
  have h11 (q : Pattern) (ha : d150069 q = 1) (hb : d202307 q = 1) : d206087 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d206087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150069, d206087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150070 q = 1) (hb : d202307 q = 1) : d206088 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d206088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150070, d206088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150071 q = 1) (hb : d202307 q = 1) : d206089 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d206089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150071, d206089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150072 q = 1) (hb : d202307 q = 1) : d206090 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d206090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150072, d206090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150073 q = 1) (hb : d202307 q = 1) : d206091 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d206091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150073, d206091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47948 (p : Pattern) (ha : d21131 p = 1) (hb : d202307 p = 1) : d206013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47930 q ha hb
    | true =>
      simp only [d20997, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20894 q = 1) (hb : d202307 q = 1) : d205901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
    | true =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
  have h5 (q : Pattern) (ha : d20895 q = 1) (hb : d202307 q = 1) : d205902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20896 q = 1) (hb : d202307 q = 1) : d205903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21000 q = 1) (hb : d202307 q = 1) : d206011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d206011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d206011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21129 q = 1) (hb : d202307 q = 1) : d205904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21129, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21130 q = 1) (hb : d202307 q = 1) : d206012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21130, d206012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21130, d206012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21131 q = 1) (hb : d202307 q = 1) : d206013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21131, d206013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21131, d206013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47949 (p : Pattern) (ha : d21135 p = 1) (hb : d202307 p = 1) : d205906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20894 q = 1) (hb : d202307 q = 1) : d205901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
    | true =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
  have h2 (q : Pattern) (ha : d20895 q = 1) (hb : d202307 q = 1) : d205902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20896 q = 1) (hb : d202307 q = 1) : d205903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21129 q = 1) (hb : d202307 q = 1) : d205904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21129, d205904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21134 q = 1) (hb : d202307 q = 1) : d205905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21134, d205905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21134, d205905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21135 q = 1) (hb : d202307 q = 1) : d205906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21135, d205906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21135, d205906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47950 (p : Pattern) (ha : d21141 p = 1) (hb : d202307 p = 1) : d206019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d202307 q = 1) : d206017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d202307 q = 1) : d206018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21141 q = 1) (hb : d202307 q = 1) : d206019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21141, d206019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21141, d206019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47951 (p : Pattern) (ha : d21145 p = 1) (hb : d202307 p = 1) : d205912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d202307 q = 1) : d205911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21145 q = 1) (hb : d202307 q = 1) : d205912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21145, d205912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21145, d205912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47952 (p : Pattern) (ha : d21151 p = 1) (hb : d202307 p = 1) : d206096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d202307 q = 1) : d206020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47950 q ha hb
    | true =>
      simp only [d21146, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47951 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d202307 q = 1) : d206092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d202307 q = 1) : d206093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d202307 q = 1) : d206094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d202307 q = 1) : d206095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21151 q = 1) (hb : d202307 q = 1) : d206096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d206096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d206096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47953 (p : Pattern) (ha : d21154 p = 1) (hb : d202307 p = 1) : d206035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d202307 q = 1) : d206017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d202307 q = 1) : d206018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d206018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21154 q = 1) (hb : d202307 q = 1) : d206035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21154, d206035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21154, d206035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47954 (p : Pattern) (ha : d21155 p = 1) (hb : d202307 p = 1) : d205919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d202307 q = 1) : d205911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d205911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21155 q = 1) (hb : d202307 q = 1) : d205919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21155, d205919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21155, d205919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47955 (p : Pattern) (ha : d21161 p = 1) (hb : d202307 p = 1) : d206103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d202307 q = 1) : d206020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47950 q ha hb
    | true =>
      simp only [d21146, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47951 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d202307 q = 1) : d206092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d202307 q = 1) : d206093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d202307 q = 1) : d206094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d202307 q = 1) : d206095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21156 q = 1) (hb : d202307 q = 1) : d206036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47953 q ha hb
    | true =>
      simp only [d21156, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47954 q ha hb
  have h7 (q : Pattern) (ha : d21157 q = 1) (hb : d202307 q = 1) : d206099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21158 q = 1) (hb : d202307 q = 1) : d206100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21158, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21159 q = 1) (hb : d202307 q = 1) : d206101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21160 q = 1) (hb : d202307 q = 1) : d206102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21161 q = 1) (hb : d202307 q = 1) : d206103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d206103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21161, d206103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47956 (p : Pattern) (ha : d21288 p = 1) (hb : d202307 p = 1) : d206185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d202307 q = 1) : d206020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47950 q ha hb
    | true =>
      simp only [d21146, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47951 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d202307 q = 1) : d206092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d206092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d202307 q = 1) : d206093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d206093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d202307 q = 1) : d206094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d206094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d202307 q = 1) : d206095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d206095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21283 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47951 q ha hb
    | true =>
      simp only [d21283, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21284 q = 1) (hb : d202307 q = 1) : d205971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21285 q = 1) (hb : d202307 q = 1) : d205972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21285, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21286 q = 1) (hb : d202307 q = 1) : d205973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21287 q = 1) (hb : d202307 q = 1) : d205974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21288 q = 1) (hb : d202307 q = 1) : d206185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21288, d206185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21288, d206185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47957 (p : Pattern) (ha : d21294 p = 1) (hb : d202307 p = 1) : d205982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21283 q = 1) (hb : d202307 q = 1) : d205913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47951 q ha hb
    | true =>
      simp only [d21283, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21284 q = 1) (hb : d202307 q = 1) : d205971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21285 q = 1) (hb : d202307 q = 1) : d205972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21285, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21286 q = 1) (hb : d202307 q = 1) : d205973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21287 q = 1) (hb : d202307 q = 1) : d205974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21289 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47954 q ha hb
    | true =>
      simp only [d21289, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21290 q = 1) (hb : d202307 q = 1) : d205978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21291 q = 1) (hb : d202307 q = 1) : d205979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21291, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21292 q = 1) (hb : d202307 q = 1) : d205980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21293 q = 1) (hb : d202307 q = 1) : d205981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21294 q = 1) (hb : d202307 q = 1) : d205982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21294, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21294, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47958 (p : Pattern) (ha : d21303 p = 1) (hb : d202307 p = 1) : d206194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21289 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47954 q ha hb
    | true =>
      simp only [d21289, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21290 q = 1) (hb : d202307 q = 1) : d205978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21291 q = 1) (hb : d202307 q = 1) : d205979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21291, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21292 q = 1) (hb : d202307 q = 1) : d205980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21293 q = 1) (hb : d202307 q = 1) : d205981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21303 q = 1) (hb : d202307 q = 1) : d206194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21303, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21303, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47959 (p : Pattern) (ha : d21342 p = 1) (hb : d202307 p = 1) : d205947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20933 q = 1) (hb : d202307 q = 1) : d205942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
    | true =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
  have h2 (q : Pattern) (ha : d20934 q = 1) (hb : d202307 q = 1) : d205943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20935 q = 1) (hb : d202307 q = 1) : d205944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21332 q = 1) (hb : d202307 q = 1) : d205945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21332, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21341 q = 1) (hb : d202307 q = 1) : d205946 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21341, d205946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21341, d205946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21342 q = 1) (hb : d202307 q = 1) : d205947 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21342, d205947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21342, d205947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47960 (p : Pattern) (ha : d21398 p = 1) (hb : d202307 p = 1) : d205953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21343 q = 1) (hb : d202307 q = 1) : d205948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47959 q ha hb
    | true =>
      simp only [d21343, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21344 q = 1) (hb : d202307 q = 1) : d205949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21395 q = 1) (hb : d202307 q = 1) : d205950 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21395, d205950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21395, d205950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21396 q = 1) (hb : d202307 q = 1) : d205951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21396, d205951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21396, d205951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21397 q = 1) (hb : d202307 q = 1) : d205952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21397, d205952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21397, d205952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21398 q = 1) (hb : d202307 q = 1) : d205953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21398, d205953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21398, d205953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47961 (p : Pattern) (ha : d21404 p = 1) (hb : d202307 p = 1) : d206240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21399 q = 1) (hb : d202307 q = 1) : d205954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21399, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47960 q ha hb
    | true =>
      simp only [d21399, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21400 q = 1) (hb : d202307 q = 1) : d206236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21400, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21400, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21401 q = 1) (hb : d202307 q = 1) : d206237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21401, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21401, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21402 q = 1) (hb : d202307 q = 1) : d206238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21402, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21402, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21403 q = 1) (hb : d202307 q = 1) : d206239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21403, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21403, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21404 q = 1) (hb : d202307 q = 1) : d206240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21404, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21404, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47962 (p : Pattern) (ha : d21166 p = 1) (hb : d202307 p = 1) : d206108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d202307 q = 1) : d206017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d202307 q = 1) : d206107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d206107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d206107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21166 q = 1) (hb : d202307 q = 1) : d206108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21166, d206108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21166, d206108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47963 (p : Pattern) (ha : d21168 p = 1) (hb : d202307 p = 1) : d205987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d202307 q = 1) : d205986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21168 q = 1) (hb : d202307 q = 1) : d205987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21168, d205987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21168, d205987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47964 (p : Pattern) (ha : d21175 p = 1) (hb : d202307 p = 1) : d206115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d202307 q = 1) : d206113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d206113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d206113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d202307 q = 1) : d206114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d206114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d206114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21175 q = 1) (hb : d202307 q = 1) : d206115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21175, d206115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21175, d206115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47965 (p : Pattern) (ha : d21178 p = 1) (hb : d202307 p = 1) : d205994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d202307 q = 1) : d205992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d202307 q = 1) : d205993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21178 q = 1) (hb : d202307 q = 1) : d205994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21178, d205994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21178, d205994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47966 (p : Pattern) (ha : d312 p = 1) (hb : d202304 p = 1) : d30744 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d311 q = 1) : d311 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d312 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d202304, d30744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312, d202304, d30744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro47967 (p : Pattern) (ha : d21182 p = 1) (hb : d202307 p = 1) : d206122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d532 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d533 q = 1) (hb : d202306 q = 1) : d206119 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d202306, d206119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d533, d202306, d206119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d538 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d539 q = 1) (hb : d202306 q = 1) : d205998 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d202306, d205998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d539, d202306, d205998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d540 q = 1) (hb : d202306 q = 1) : d206120 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d206120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d540, d206120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d541 q = 1) (hb : d202306 q = 1) : d206121 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d206121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d541, d206121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21182 q = 1) (hb : d202307 q = 1) : d206122 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21182, d202307, d206122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21182, d202307, d206122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro47968 (p : Pattern) (ha : d5011 p = 1) (hb : d202304 p = 1) : d206128 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5010 q = 1) : d5010 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5011 q = 1) (hb : d202304 q = 1) : d206128 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d5011, d202304, d206128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5011, d202304, d206128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro47969 (p : Pattern) (ha : d21188 p = 1) (hb : d202307 p = 1) : d206134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d314 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9452 q = 1) (hb : d202304 q = 1) : d206129 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d206129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47968 q ha hb
    | true =>
      simp only [d9452, d206129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9453 q = 1) (hb : d202304 q = 1) : d206130 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d206130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9453, d206130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9464 q = 1) (hb : d202306 q = 1) : d206131 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d202306, d206131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9464, d202306, d206131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d202306 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9465 q = 1) (hb : d202306 q = 1) : d206132 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d206132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9465, d206132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9466 q = 1) (hb : d202306 q = 1) : d206133 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d206133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9466, d206133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d21188 q = 1) (hb : d202307 q = 1) : d206134 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21188, d202307, d206134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21188, d202307, d206134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro47970 (p : Pattern) (ha : d21194 p = 1) (hb : d202307 p = 1) : d206140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d202307 q = 1) : d206123 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
    | true =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d202307 q = 1) : d206124 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d202307 q = 1) : d206125 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d206125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d206125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d202307 q = 1) : d206126 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d206126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d206126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d202307 q = 1) : d206004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d202307 q = 1) : d206005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21187 q = 1) (hb : d202307 q = 1) : d206127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d206127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21187, d206127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21191 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21192 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d5451 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
    | true =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d5452 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d5453 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5454 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5454, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21193 q = 1) (hb : d202307 q = 1) : d206139 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21193, d206139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21193, d206139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21194 q = 1) (hb : d202307 q = 1) : d206140 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21194, d206140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21194, d206140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47971 (p : Pattern) (ha : d21198 p = 1) (hb : d202307 p = 1) : d205900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5451 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
    | true =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5452 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5453 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5454 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5454, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20995 q = 1) (hb : d202307 q = 1) : d205899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20995, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21198 q = 1) (hb : d202307 q = 1) : d205900 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21198, d205900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21198, d205900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47972 (p : Pattern) (ha : d21204 p = 1) (hb : d202307 p = 1) : d206146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21195 q = 1) (hb : d202307 q = 1) : d206141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21195, d206141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47970 q ha hb
    | true =>
      simp only [d21195, d206141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47930 q ha hb
  have h2 (q : Pattern) (ha : d21196 q = 1) (hb : d202307 q = 1) : d206142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21196, d206142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21196, d206142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21197 q = 1) (hb : d202307 q = 1) : d206143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21197, d206143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21197, d206143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21199 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21199, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47930 q ha hb
    | true =>
      simp only [d21199, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47971 q ha hb
  have h5 (q : Pattern) (ha : d21200 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21200, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21200, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21201 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21201, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21201, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21202 q = 1) (hb : d202307 q = 1) : d206144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21202, d206144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21202, d206144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20997 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47930 q ha hb
    | true =>
      simp only [d20997, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
  have h9 (q : Pattern) (ha : d20998 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20999 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20894 q = 1) (hb : d202307 q = 1) : d205901 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47906 q ha hb
    | true =>
      simp only [d20894, d205901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47888 q ha hb
  have h12 (q : Pattern) (ha : d20895 q = 1) (hb : d202307 q = 1) : d205902 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d205902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20896 q = 1) (hb : d202307 q = 1) : d205903 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d205903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21000 q = 1) (hb : d202307 q = 1) : d206011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d206011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21000, d206011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21203 q = 1) (hb : d202307 q = 1) : d206145 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21203, d206145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21203, d206145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21204 q = 1) (hb : d202307 q = 1) : d206146 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21204, d206146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21204, d206146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro47973 (p : Pattern) (ha : d21210 p = 1) (hb : d202307 p = 1) : d206152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d202307 q = 1) : d206147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d206147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47972 q ha hb
    | true =>
      simp only [d21205, d206147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d202307 q = 1) : d206148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d206148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d206148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d202307 q = 1) : d206149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d206149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d206149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d202307 q = 1) : d206150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d206150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d206150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d202307 q = 1) : d206151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d206151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d206151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21210 q = 1) (hb : d202307 q = 1) : d206152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21210, d206152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21210, d206152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47974 (p : Pattern) (ha : d21251 p = 1) (hb : d202307 p = 1) : d206158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d202307 q = 1) : d206155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d206155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d206155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d202307 q = 1) : d206156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d206156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d206156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d202307 q = 1) : d206157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d206157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d206157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21251 q = 1) (hb : d202307 q = 1) : d206158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21251, d206158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21251, d206158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47975 (p : Pattern) (ha : d150078 p = 1) (hb : d202307 p = 1) : d206164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d202307 q = 1) : d206109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d206109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47962 q ha hb
    | true =>
      simp only [d21169, d206109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47963 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d202307 q = 1) : d206110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d206110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d206110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d202307 q = 1) : d206111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d206111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d206111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d202307 q = 1) : d206112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d206112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d206112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d202307 q = 1) : d206116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d206116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47964 q ha hb
    | true =>
      simp only [d21179, d206116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47965 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d202307 q = 1) : d206117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d206117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d206117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d202307 q = 1) : d206118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d206118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d206118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d202307 q = 1) : d206153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d206153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47973 q ha hb
    | true =>
      simp only [d21211, d206153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47950 q ha hb
  have h9 (q : Pattern) (ha : d150074 q = 1) (hb : d202307 q = 1) : d206154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d206154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150074, d206154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d202307 q = 1) : d206159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d206159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47974 q ha hb
    | true =>
      simp only [d21252, d206159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d202307 q = 1) : d206160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d206160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d206160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150075 q = 1) (hb : d202307 q = 1) : d206161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d206161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d206161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150076 q = 1) (hb : d202307 q = 1) : d206162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d206162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150076, d206162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150077 q = 1) (hb : d202307 q = 1) : d206163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d206163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150077, d206163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150078 q = 1) (hb : d202307 q = 1) : d206164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d206164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150078, d206164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47976 (p : Pattern) (ha : d21258 p = 1) (hb : d202307 p = 1) : d206165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d202307 q = 1) : d206017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d206017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d202307 q = 1) : d206107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d206107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d206107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21258 q = 1) (hb : d202307 q = 1) : d206165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21258, d206165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21258, d206165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47977 (p : Pattern) (ha : d21259 p = 1) (hb : d202307 p = 1) : d206026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d202307 q = 1) : d205910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d205910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d202307 q = 1) : d205986 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d205986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21259 q = 1) (hb : d202307 q = 1) : d206026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21259, d206026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21259, d206026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47978 (p : Pattern) (ha : d21264 p = 1) (hb : d202307 p = 1) : d206170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d202307 q = 1) : d206016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d206016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d202307 q = 1) : d206113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d206113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d206113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d202307 q = 1) : d206114 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d206114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d206114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21264 q = 1) (hb : d202307 q = 1) : d206170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21264, d206170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21264, d206170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47979 (p : Pattern) (ha : d21265 p = 1) (hb : d202307 p = 1) : d206031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d202307 q = 1) : d205907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47949 q ha hb
    | true =>
      simp only [d21136, d205907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d202307 q = 1) : d205908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d205908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d202307 q = 1) : d205909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d205909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d202307 q = 1) : d205992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d205992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d202307 q = 1) : d205993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d205993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21265 q = 1) (hb : d202307 q = 1) : d206031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21265, d206031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21265, d206031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47980 (p : Pattern) (ha : d21269 p = 1) (hb : d202307 p = 1) : d206174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d202307 q = 1) : d206147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d206147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47972 q ha hb
    | true =>
      simp only [d21205, d206147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d202307 q = 1) : d206148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d206148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d206148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d202307 q = 1) : d206149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d206149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d206149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d202307 q = 1) : d206150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d206150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d206150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d202307 q = 1) : d206151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d206151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d206151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21269 q = 1) (hb : d202307 q = 1) : d206174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21269, d206174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21269, d206174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47981 (p : Pattern) (ha : d21275 p = 1) (hb : d202307 p = 1) : d206177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d202307 q = 1) : d206014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47948 q ha hb
    | true =>
      simp only [d21132, d206014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d202307 q = 1) : d206015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d206015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d202307 q = 1) : d206155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d206155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d206155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d202307 q = 1) : d206156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d206156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d206156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d202307 q = 1) : d206157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d206157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d206157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21275 q = 1) (hb : d202307 q = 1) : d206177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21275, d206177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21275, d206177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47982 (p : Pattern) (ha : d150083 p = 1) (hb : d202307 p = 1) : d206183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d202307 q = 1) : d206109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d206109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47962 q ha hb
    | true =>
      simp only [d21169, d206109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47963 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d202307 q = 1) : d206110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d206110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d206110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d202307 q = 1) : d206111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d206111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d206111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d202307 q = 1) : d206112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d206112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d206112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d202307 q = 1) : d206116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d206116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47964 q ha hb
    | true =>
      simp only [d21179, d206116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47965 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d202307 q = 1) : d206117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d206117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d206117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d202307 q = 1) : d206118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d206118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d206118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d202307 q = 1) : d206153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d206153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47973 q ha hb
    | true =>
      simp only [d21211, d206153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47950 q ha hb
  have h9 (q : Pattern) (ha : d150074 q = 1) (hb : d202307 q = 1) : d206154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d206154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150074, d206154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d202307 q = 1) : d206159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d206159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47974 q ha hb
    | true =>
      simp only [d21252, d206159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d202307 q = 1) : d206160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d206160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d206160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150075 q = 1) (hb : d202307 q = 1) : d206161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d206161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d206161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150076 q = 1) (hb : d202307 q = 1) : d206162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d206162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150076, d206162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150077 q = 1) (hb : d202307 q = 1) : d206163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d206163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150077, d206163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21260 q = 1) (hb : d202307 q = 1) : d206166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21260, d206166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47976 q ha hb
    | true =>
      simp only [d21260, d206166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47977 q ha hb
  have h16 (q : Pattern) (ha : d21261 q = 1) (hb : d202307 q = 1) : d206167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21261, d206167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21261, d206167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21262 q = 1) (hb : d202307 q = 1) : d206168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21262, d206168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21262, d206168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21263 q = 1) (hb : d202307 q = 1) : d206169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21263, d206169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21263, d206169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21266 q = 1) (hb : d202307 q = 1) : d206171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21266, d206171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47978 q ha hb
    | true =>
      simp only [d21266, d206171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47979 q ha hb
  have h20 (q : Pattern) (ha : d21267 q = 1) (hb : d202307 q = 1) : d206172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21267, d206172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21267, d206172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21268 q = 1) (hb : d202307 q = 1) : d206173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21268, d206173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21268, d206173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21270 q = 1) (hb : d202307 q = 1) : d206175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d206175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47980 q ha hb
    | true =>
      simp only [d21270, d206175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47953 q ha hb
  have h23 (q : Pattern) (ha : d150079 q = 1) (hb : d202307 q = 1) : d206176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d206176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150079, d206176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21276 q = 1) (hb : d202307 q = 1) : d206178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d206178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47981 q ha hb
    | true =>
      simp only [d21276, d206178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21277 q = 1) (hb : d202307 q = 1) : d206179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d206179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21277, d206179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150080 q = 1) (hb : d202307 q = 1) : d206180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d206180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150080, d206180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150081 q = 1) (hb : d202307 q = 1) : d206181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d206181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150081, d206181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150082 q = 1) (hb : d202307 q = 1) : d206182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d206182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150082, d206182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150083 q = 1) (hb : d202307 q = 1) : d206183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d206183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150083, d206183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro47983 (p : Pattern) (ha : d150090 p = 1) (hb : d202307 p = 1) : d206192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21270 q = 1) (hb : d202307 q = 1) : d206175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d206175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47980 q ha hb
    | true =>
      simp only [d21270, d206175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47953 q ha hb
  have h2 (q : Pattern) (ha : d150079 q = 1) (hb : d202307 q = 1) : d206176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d206176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150079, d206176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21276 q = 1) (hb : d202307 q = 1) : d206178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d206178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47981 q ha hb
    | true =>
      simp only [d21276, d206178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21277 q = 1) (hb : d202307 q = 1) : d206179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d206179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21277, d206179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150080 q = 1) (hb : d202307 q = 1) : d206180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d206180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150080, d206180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150088 q = 1) (hb : d202307 q = 1) : d206190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d206190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150088, d206190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150089 q = 1) (hb : d202307 q = 1) : d206191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d206191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150089, d206191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150090 q = 1) (hb : d202307 q = 1) : d206192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d206192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150090, d206192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47984 (p : Pattern) (ha : d21319 p = 1) (hb : d202307 p = 1) : d206210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d202307 q = 1) : d206200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d206200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d206200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d202307 q = 1) : d206123 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
    | true =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d202307 q = 1) : d206201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d206201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d206201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d202307 q = 1) : d206124 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d202307 q = 1) : d206202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d206202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d206202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d202307 q = 1) : d206203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d206203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d206203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21071 q = 1) (hb : d202307 q = 1) : d206056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d206056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
  have h8 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21072 q = 1) (hb : d202307 q = 1) : d206057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21072, d206057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21073 q = 1) (hb : d202307 q = 1) : d206058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21073, d206058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21074 q = 1) (hb : d202307 q = 1) : d206059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21074, d206059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21313 q = 1) (hb : d202307 q = 1) : d206204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d206204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21313, d206204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21314 q = 1) (hb : d202307 q = 1) : d206205 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d206205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
  have h15 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d21315 q = 1) (hb : d202307 q = 1) : d206206 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21315, d206206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21316 q = 1) (hb : d202307 q = 1) : d206207 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21316, d206207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21317 q = 1) (hb : d202307 q = 1) : d206208 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d21317, d206208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d5495 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
  have h21 (q : Pattern) (ha : d5451 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
    | true =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d5496 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d5496, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d5452 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5497 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d5497, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d5498 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5498, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21318 q = 1) (hb : d202307 q = 1) : d206209 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21318, d206209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21318, d206209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d21319 q = 1) (hb : d202307 q = 1) : d206210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21319, d206210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21319, d206210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro47985 (p : Pattern) (ha : d21323 p = 1) (hb : d202307 p = 1) : d205941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5495 q = 1) (hb : d202307 q = 1) : d205936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d205936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
  have h2 (q : Pattern) (ha : d5451 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47927 q ha hb
    | true =>
      simp only [d5451, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5496 q = 1) (hb : d202307 q = 1) : d205937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5496, d205937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5452 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5452, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5497 q = 1) (hb : d202307 q = 1) : d205938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5497, d205938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5498 q = 1) (hb : d202307 q = 1) : d205939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5498, d205939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47887 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21076 q = 1) (hb : d202307 q = 1) : d205940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21076, d205940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d21323 q = 1) (hb : d202307 q = 1) : d205941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21323, d205941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21323, d205941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro47986 (p : Pattern) (ha : d21329 p = 1) (hb : d202307 p = 1) : d206216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21320 q = 1) (hb : d202307 q = 1) : d206211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21320, d206211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47984 q ha hb
    | true =>
      simp only [d21320, d206211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47941 q ha hb
  have h2 (q : Pattern) (ha : d21321 q = 1) (hb : d202307 q = 1) : d206212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21321, d206212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21321, d206212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21322 q = 1) (hb : d202307 q = 1) : d206213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21322, d206213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21322, d206213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21324 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21324, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47941 q ha hb
    | true =>
      simp only [d21324, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47985 q ha hb
  have h5 (q : Pattern) (ha : d21325 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21325, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21325, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21326 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21326, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21326, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21327 q = 1) (hb : d202307 q = 1) : d206214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21327, d206214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21327, d206214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21078 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47941 q ha hb
    | true =>
      simp only [d21078, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
  have h9 (q : Pattern) (ha : d21079 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21080 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20933 q = 1) (hb : d202307 q = 1) : d205942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
    | true =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
  have h12 (q : Pattern) (ha : d20934 q = 1) (hb : d202307 q = 1) : d205943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20935 q = 1) (hb : d202307 q = 1) : d205944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21081 q = 1) (hb : d202307 q = 1) : d206065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d206065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21081, d206065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21328 q = 1) (hb : d202307 q = 1) : d206215 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21328, d206215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21328, d206215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21329 q = 1) (hb : d202307 q = 1) : d206216 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21329, d206216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d21329, d206216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro47987 (p : Pattern) (ha : d21334 p = 1) (hb : d202307 p = 1) : d206067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d202307 q = 1) : d206062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47941 q ha hb
    | true =>
      simp only [d21078, d206062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d202307 q = 1) : d206063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d206063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d202307 q = 1) : d206064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d206064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20933 q = 1) (hb : d202307 q = 1) : d205942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47915 q ha hb
    | true =>
      simp only [d20933, d205942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47895 q ha hb
  have h5 (q : Pattern) (ha : d20934 q = 1) (hb : d202307 q = 1) : d205943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d205943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20935 q = 1) (hb : d202307 q = 1) : d205944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d205944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21081 q = 1) (hb : d202307 q = 1) : d206065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d206065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d206065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21332 q = 1) (hb : d202307 q = 1) : d205945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21332, d205945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21333 q = 1) (hb : d202307 q = 1) : d206066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21333, d206066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21333, d206066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21334 q = 1) (hb : d202307 q = 1) : d206067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21334, d206067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21334, d206067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47988 (p : Pattern) (ha : d21340 p = 1) (hb : d202307 p = 1) : d206222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21330 q = 1) (hb : d202307 q = 1) : d206217 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21330, d206217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47986 q ha hb
    | true =>
      simp only [d21330, d206217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21331 q = 1) (hb : d202307 q = 1) : d206218 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21331, d206218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21331, d206218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21335 q = 1) (hb : d202307 q = 1) : d206068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47987 q ha hb
    | true =>
      simp only [d21335, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21336 q = 1) (hb : d202307 q = 1) : d206069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21337 q = 1) (hb : d202307 q = 1) : d206219 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21337, d206219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21337, d206219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21338 q = 1) (hb : d202307 q = 1) : d206220 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21338, d206220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21338, d206220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21339 q = 1) (hb : d202307 q = 1) : d206221 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21339, d206221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21339, d206221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21340 q = 1) (hb : d202307 q = 1) : d206222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21340, d206222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21340, d206222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47989 (p : Pattern) (ha : d21348 p = 1) (hb : d202307 p = 1) : d206073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d202307 q = 1) : d206068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47987 q ha hb
    | true =>
      simp only [d21335, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d202307 q = 1) : d206069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21343 q = 1) (hb : d202307 q = 1) : d205948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47959 q ha hb
    | true =>
      simp only [d21343, d205948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21344 q = 1) (hb : d202307 q = 1) : d205949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d205949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21345 q = 1) (hb : d202307 q = 1) : d206070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21345, d206070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21345, d206070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21346 q = 1) (hb : d202307 q = 1) : d206071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21346, d206071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21346, d206071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21347 q = 1) (hb : d202307 q = 1) : d206072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21347, d206072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21347, d206072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21348 q = 1) (hb : d202307 q = 1) : d206073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21348, d206073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21348, d206073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro47990 (p : Pattern) (ha : d21387 p = 1) (hb : d202307 p = 1) : d206228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d202307 q = 1) : d206068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47987 q ha hb
    | true =>
      simp only [d21335, d206068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d202307 q = 1) : d206069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d206069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21384 q = 1) (hb : d202307 q = 1) : d206225 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21384, d206225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21384, d206225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21385 q = 1) (hb : d202307 q = 1) : d206226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21385, d206226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21385, d206226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21386 q = 1) (hb : d202307 q = 1) : d206227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21386, d206227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21386, d206227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21387 q = 1) (hb : d202307 q = 1) : d206228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21387, d206228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21387, d206228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47991 (p : Pattern) (ha : d150100 p = 1) (hb : d202307 p = 1) : d206234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21349 q = 1) (hb : d202307 q = 1) : d206223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21349, d206223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47988 q ha hb
    | true =>
      simp only [d21349, d206223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47989 q ha hb
  have h2 (q : Pattern) (ha : d150096 q = 1) (hb : d202307 q = 1) : d206224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d206224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150096, d206224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21388 q = 1) (hb : d202307 q = 1) : d206229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21388, d206229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47990 q ha hb
    | true =>
      simp only [d21388, d206229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21389 q = 1) (hb : d202307 q = 1) : d206230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21389, d206230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21389, d206230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150097 q = 1) (hb : d202307 q = 1) : d206231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d206231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150097, d206231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150098 q = 1) (hb : d202307 q = 1) : d206232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d206232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150098, d206232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150099 q = 1) (hb : d202307 q = 1) : d206233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d206233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150099, d206233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150100 q = 1) (hb : d202307 q = 1) : d206234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d206234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150100, d206234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro47992 (p : Pattern) (ha : d150106 p = 1) (hb : d202307 p = 1) : d206246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21152 q = 1) (hb : d202307 q = 1) : d206097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21152, d206097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21152, d206097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47952 q ha hb
  have h2 (q : Pattern) (ha : d21153 q = 1) (hb : d202307 q = 1) : d206098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21153, d206098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21153, d206098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21162 q = 1) (hb : d202307 q = 1) : d206104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47952 q ha hb
    | true =>
      simp only [d21162, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47955 q ha hb
  have h4 (q : Pattern) (ha : d21163 q = 1) (hb : d202307 q = 1) : d206105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21163, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21164 q = 1) (hb : d202307 q = 1) : d206106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21164, d206106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21164, d206106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150084 q = 1) (hb : d202307 q = 1) : d206184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d206184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47975 q ha hb
    | true =>
      simp only [d150084, d206184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47982 q ha hb
  have h7 (q : Pattern) (ha : d21295 q = 1) (hb : d202307 q = 1) : d206186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21295, d206186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47956 q ha hb
    | true =>
      simp only [d21295, d206186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47957 q ha hb
  have h8 (q : Pattern) (ha : d150085 q = 1) (hb : d202307 q = 1) : d206187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d206187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150085, d206187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150086 q = 1) (hb : d202307 q = 1) : d206188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d206188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150086, d206188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150087 q = 1) (hb : d202307 q = 1) : d206189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d206189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150087, d206189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150091 q = 1) (hb : d202307 q = 1) : d206193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d206193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150091, d206193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47983 q ha hb
  have h12 (q : Pattern) (ha : d21304 q = 1) (hb : d202307 q = 1) : d206195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21304, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21304, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47958 q ha hb
  have h13 (q : Pattern) (ha : d150092 q = 1) (hb : d202307 q = 1) : d206196 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d206196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150092, d206196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150093 q = 1) (hb : d202307 q = 1) : d206197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d206197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150093, d206197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150094 q = 1) (hb : d202307 q = 1) : d206198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d206198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150094, d206198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150095 q = 1) (hb : d202307 q = 1) : d206199 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d206199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150095, d206199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150101 q = 1) (hb : d202307 q = 1) : d206235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d206235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150101, d206235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47991 q ha hb
  have h18 (q : Pattern) (ha : d21405 q = 1) (hb : d202307 q = 1) : d206241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21405, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21405, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47961 q ha hb
  have h19 (q : Pattern) (ha : d150102 q = 1) (hb : d202307 q = 1) : d206242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d206242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150102, d206242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150103 q = 1) (hb : d202307 q = 1) : d206243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d206243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150103, d206243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150104 q = 1) (hb : d202307 q = 1) : d206244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d206244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150104, d206244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150105 q = 1) (hb : d202307 q = 1) : d206245 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d206245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150105, d206245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150106 q = 1) (hb : d202307 q = 1) : d206246 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d206246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150106, d206246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro47993 (p : Pattern) (ha : d150112 p = 1) (hb : d202307 p = 1) : d206252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d202307 q = 1) : d206247 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d206247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d206247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47992 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d202307 q = 1) : d206248 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d206248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d206248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d202307 q = 1) : d206249 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d206249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d206249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d202307 q = 1) : d206250 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d206250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d206250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d202307 q = 1) : d206251 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d206251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d206251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d202307 q = 1) : d206252 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d206252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d206252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro47994 (p : Pattern) (ha : d762 p = 1) (hb : d202307 p = 1) : d205900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d202307 q = 1) : d205899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d202307 q = 1) : d205900 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d205900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d205900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47995 (p : Pattern) (ha : d21419 p = 1) (hb : d202307 p = 1) : d206140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d202307 q = 1) : d206123 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47967 q ha hb
    | true =>
      simp only [d21183, d206123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d202307 q = 1) : d206124 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d206124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d202307 q = 1) : d206125 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d206125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d206125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d202307 q = 1) : d206126 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d206126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d206126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20992 q = 1) (hb : d202307 q = 1) : d206004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20993 q = 1) (hb : d202307 q = 1) : d206005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21187 q = 1) (hb : d202307 q = 1) : d206127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d206127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21187, d206127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21189 q = 1) (hb : d202307 q = 1) : d206135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47969 q ha hb
    | true =>
      simp only [d21189, d206135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21190 q = 1) (hb : d202307 q = 1) : d206136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21190, d206136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21191 q = 1) (hb : d202307 q = 1) : d206137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d206137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21192 q = 1) (hb : d202307 q = 1) : d206138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21192, d206138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21418 q = 1) (hb : d202307 q = 1) : d206139 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d206139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21418, d206139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21419 q = 1) (hb : d202307 q = 1) : d206140 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21419, d206140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21419, d206140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro47996 (p : Pattern) (ha : d21420 p = 1) (hb : d202307 p = 1) : d206007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d202307 q = 1) : d206002 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47929 q ha hb
    | true =>
      simp only [d20990, d206002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d202307 q = 1) : d206003 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d206003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d202307 q = 1) : d206004 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d206004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d202307 q = 1) : d206005 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d206005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d202307 q = 1) : d205895 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47905 q ha hb
    | true =>
      simp only [d751, d205895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d202307 q = 1) : d205896 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d205896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d202307 q = 1) : d205897 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d205897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d202307 q = 1) : d205898 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d205898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20994 q = 1) (hb : d202307 q = 1) : d206006 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d206006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20994, d206006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d202307 q = 1) : d205899 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d205899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21420 q = 1) (hb : d202307 q = 1) : d206007 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21420, d206007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21420, d206007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro47997 (p : Pattern) (ha : d21430 p = 1) (hb : d202307 p = 1) : d206256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21421 q = 1) (hb : d202307 q = 1) : d206141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d206141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47995 q ha hb
    | true =>
      simp only [d21421, d206141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47996 q ha hb
  have h2 (q : Pattern) (ha : d21422 q = 1) (hb : d202307 q = 1) : d206142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d206142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d206142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21423 q = 1) (hb : d202307 q = 1) : d206143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d206143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d206143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21424 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47996 q ha hb
    | true =>
      simp only [d21424, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47994 q ha hb
  have h5 (q : Pattern) (ha : d21425 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21426 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21427 q = 1) (hb : d202307 q = 1) : d206144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d206144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21427, d206144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21428 q = 1) (hb : d202307 q = 1) : d206254 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d206254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21428, d206254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21429 q = 1) (hb : d202307 q = 1) : d206255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21429, d206255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21429, d206255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21430 q = 1) (hb : d202307 q = 1) : d206256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21430, d206256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21430, d206256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro47998 (p : Pattern) (ha : d21434 p = 1) (hb : d202307 p = 1) : d206260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21424 q = 1) (hb : d202307 q = 1) : d206008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47996 q ha hb
    | true =>
      simp only [d21424, d206008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47994 q ha hb
  have h2 (q : Pattern) (ha : d21425 q = 1) (hb : d202307 q = 1) : d206009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d206009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21426 q = 1) (hb : d202307 q = 1) : d206010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d206010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21428 q = 1) (hb : d202307 q = 1) : d206254 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d206254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21428, d206254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21433 q = 1) (hb : d202307 q = 1) : d206259 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21433, d206259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21433, d206259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21434 q = 1) (hb : d202307 q = 1) : d206260 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21434, d206260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21434, d206260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro47999 (p : Pattern) (ha : d21440 p = 1) (hb : d202307 p = 1) : d206266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d202307 q = 1) : d206257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47997 q ha hb
    | true =>
      simp only [d21431, d206257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d202307 q = 1) : d206258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d206258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d202307 q = 1) : d206261 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47998 q ha hb
    | true =>
      simp only [d21435, d206261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d202307 q = 1) : d206262 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d206262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d202307 q = 1) : d206263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d206263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d202307 q = 1) : d206264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d206264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d202307 q = 1) : d206265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d206265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d206265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21440 q = 1) (hb : d202307 q = 1) : d206266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21440, d206266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21440, d206266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
